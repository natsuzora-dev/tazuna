import { relative, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { z } from "zod";
import { sorted } from "../data/collections.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Malformed } from "../data/malformed.ts";
import type { GivenRecord, PeerEntry, Scenario } from "../data/scenario.generated.ts";
import { strictObjectOf } from "../data/values.ts";
import type { Named, Place, ServiceDefinition } from "../dsl/definition.ts";
import type { AnyEntity } from "../dsl/entity.ts";
import { contractService } from "../dsl/service.ts";
import type { ScenarioDefinition } from "../scenario/define.ts";
import { instant, type LoweringProblem, lower } from "../scenario/lower.ts";
import type { Structure } from "../syntax/structure.generated.ts";
import type { Found } from "./found.ts";

/** A scenario as data, with the place in the scenario file of each of its lines. */
export interface LoadedScenario {
  readonly description: string;
  readonly scenario: Scenario;
  readonly linePlaces: readonly (Place | undefined)[];
}

type Services = ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>;

/** The first frame of `stack` in a file under `root` outside node_modules, as a place relative to `root`. */
function placeInStack(root: string, stack: string | undefined): Place | undefined {
  for (const match of (stack ?? "").matchAll(/\((file:\/\/[^)]+):(\d+):(\d+)\)|at (file:\/\/\S+):(\d+):(\d+)/g)) {
    const url = match[1] ?? match[4];
    if (url === undefined) continue;
    const file = relative(root, fileURLToPath(url));
    if (file.startsWith("..") || file.split(sep).includes("node_modules")) continue;
    return {
      file: file.split(sep).join("/"),
      line: Number(match[2] ?? match[5]),
      column: Number(match[3] ?? match[6]),
    };
  }
  return undefined;
}

/**
 * The services that the own service exchanges messages with: those whose definitions its definitions name, and the
 * spec services whose definitions name its definitions.
 */
function peersOf(structure: Structure, own: string): string[] {
  const named = (d: Structure["definitions"][number]): (DefinitionRef | null)[] => {
    switch (d.kind) {
      case "automation":
        return [d.receives, d.command];
      case "machine":
      case "screen":
        return [
          ...Object.values(d.receives),
          ...Object.values(d.commands),
          ...Object.values(d.queries),
          ...Object.values(d.screens),
        ];
      default:
        return [];
    }
  };
  const external = new Set(structure.services.filter((s) => s.external).map((s) => s.name));
  const found = new Set<string>();
  for (const d of structure.definitions)
    for (const r of named(d)) {
      if (r === null || r.service === d.service) continue;
      if (d.service === own) found.add(r.service);
      else if (r.service === own && !external.has(d.service)) found.add(d.service);
    }
  return [...found].sort();
}

type Problem = Malformed & { readonly scenario: DefinitionRef };

/** The Given records of `service` as data, each parsed by its entity's schema and encoded, or the problems. */
function givenRecords(
  scenario: DefinitionRef,
  service: string,
  entities: Readonly<Record<string, AnyEntity>>,
  records: unknown,
): { readonly records: GivenRecord[]; readonly problems: Problem[] } {
  const found: GivenRecord[] = [];
  const problems: Problem[] = [];
  const invalid = (entity: string, key?: string) =>
    problems.push({
      kind: "Malformed.invalidRecord",
      definition: null,
      scenario,
      data: { service, entity, ...(key === undefined ? {} : { key }) },
    });
  const encoded = (e: AnyEntity, value: unknown): unknown => {
    const object = strictObjectOf(e.fields);
    const parsed = object.safeParse(value);
    if (!parsed.success) return undefined;
    const r = z.safeEncode(object, sorted(object, parsed.data) as never);
    return r.success ? r.data : undefined;
  };
  for (const [entity, written] of Object.entries((records ?? {}) as Record<string, unknown>)) {
    const e = entities[entity];
    if (e === undefined) {
      invalid(entity);
      continue;
    }
    if (e.single) {
      const value = encoded(e, written);
      if (value === undefined) invalid(entity);
      else found.push({ entity, value });
      continue;
    }
    for (const row of Array.isArray(written) ? written : []) {
      const key = (row as Record<string, unknown>)[e.key];
      const value = encoded(e, row);
      if (typeof key !== "string" || value === undefined) invalid(entity, typeof key === "string" ? key : undefined);
      else found.push({ entity, key, value });
    }
  }
  return { records: found, problems };
}

function loweringMalformed(scenario: DefinitionRef, p: LoweringProblem): Problem {
  switch (p.kind) {
    case "unnamed":
      return {
        kind: "Malformed.unexportedDefinition",
        definition: null,
        scenario,
        data: { name: scenario.name, path: p.path },
      } as Problem;
    case "lineAfterWhen":
      return { kind: "Malformed.lineAfterWhen", definition: null, scenario, data: {} };
    case "unparsableTime":
      return { kind: "Malformed.unparsableTime", definition: null, scenario, input: p.line + 1, data: {} } as Problem;
  }
}

/**
 * Reads each scenario as data: Given's records parsed and encoded, its peers by service, and When and Then lowered.
 * Reports what it cannot read, and each service that the own service exchanges messages with and Given does not list.
 */
export function loadScenarios(
  root: string,
  written: readonly Named<ScenarioDefinition>[],
  services: Services,
  structure: Structure,
  refOf: (definition: unknown) => DefinitionRef | undefined,
): { readonly scenarios: Named<LoadedScenario>[]; readonly malformed: Found<Malformed>[] } {
  const serviceNames = new Map([...services].map(([name, s]) => [s.definition, name]));
  const malformed: Found<Malformed>[] = [];
  const scenarios = written.map((named): Named<LoadedScenario> => {
    const { service: own, place, definition } = named;
    const ref = { service: own, name: named.name };
    const report = (problem: Problem) => malformed.push({ violation: problem, place });
    const entitiesOf = (service: string) => services.get(service)?.definition.entities ?? {};
    const ownRecords = givenRecords(ref, own, entitiesOf(own), definition.given.records);
    ownRecords.problems.forEach(report);
    const peers: PeerEntry[] = Object.entries(definition.given.peers).flatMap(([key, entry]): PeerEntry[] => {
      const owner = contractService(entry.contract);
      const service = owner === undefined ? undefined : serviceNames.get(owner);
      if (service === undefined || service === own) {
        report({ kind: "Malformed.unknownPeer", definition: null, scenario: ref, data: { service: service ?? null } });
        return [];
      }
      if (service !== key) {
        report({ kind: "Malformed.misnamedPeer", definition: null, scenario: ref, data: { name: key, service } });
        return [];
      }
      if (entry.role === "external") return [{ service, role: "external" }];
      if (entry.role === "skip") return [{ service, role: "skip", because: entry.because }];
      const peerRecords = givenRecords(ref, service, entitiesOf(service), entry.records);
      peerRecords.problems.forEach(report);
      return [{ service, role: "run", records: peerRecords.records }];
    });
    const listed = new Set(peers.map((p) => p.service));
    for (const service of peersOf(structure, own))
      if (!listed.has(service))
        report({ kind: "Malformed.unlistedPeer", definition: null, scenario: ref, data: { service } });
    const start = instant(definition.given.start);
    if (start === undefined)
      report({ kind: "Malformed.unparsableTime", definition: null, scenario: ref, input: 0, data: {} } as Problem);
    const lowered = lower(definition, refOf);
    for (const p of lowered.problems) report(loweringMalformed(ref, p));
    return {
      ...named,
      definition: {
        description: definition.description,
        scenario: {
          service: own,
          given: { start: start ?? definition.given.start, records: ownRecords.records, peers },
          lines: [...lowered.lines],
          expectations: [...lowered.expectations],
        },
        linePlaces: lowered.stacks.map((s) => placeInStack(root, s)),
      },
    };
  });
  return { scenarios, malformed };
}
