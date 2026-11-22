import { relative, sep } from "node:path";
import { fileURLToPath } from "node:url";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Malformed } from "../data/malformed.ts";
import type { GivenRecord, PeerEntry, Scenario } from "../data/scenario.generated.ts";
import { plain, stringsOf } from "../data/values.ts";
import type { Named, Place, ServiceDefinition } from "../dsl/definition.ts";
import type { AnyEntity } from "../dsl/entity.ts";
import { contractService } from "../dsl/service.ts";
import type { ScenarioDefinition } from "../scenario/define.ts";
import { type LoweringViolation, lower } from "../scenario/lower.ts";
import { isKeyOf } from "../spec/structure.ts";
import type { Found } from "./found.ts";

export interface LoadedScenario {
  readonly description: string;
  readonly scenario: Scenario;
  readonly linePlaces: readonly (Place | undefined)[];
  readonly expectationPlaces: readonly (Place | undefined)[];
}

type Services = ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>;

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
 * The first string of `value` in the form of a key that a spec service creates (`<service>/<Entity>-<n>` of a keyed
 * entity), with that entity. A scenario never writes such a key: it reads one through a handle, and a running peer's
 * answer writes `created()`.
 */
function writtenKey(
  services: Services,
  value: unknown,
): { readonly key: string; readonly entity: DefinitionRef } | undefined {
  for (const key of stringsOf(value))
    for (const [service, { definition }] of services) {
      if (definition.external) continue;
      const entity = Object.entries(definition.entities).find(
        ([name, e]) => !e.single && isKeyOf(`${service}/${name}`, key),
      )?.[0];
      if (entity !== undefined) return { key, entity: { service, name: entity } };
    }
  return undefined;
}

/**
 * The Given records of a service as data, each as written, with its key when its entity is keyed; the simulation checks
 * them (InvalidScenario.invalidRecord).
 */
function givenRecords(entities: Readonly<Record<string, AnyEntity>>, records: unknown): GivenRecord[] {
  return Object.entries((records ?? {}) as Record<string, unknown>).flatMap(([entity, written]): GivenRecord[] => {
    const e = entities[entity];
    if (e === undefined || e.single || !Array.isArray(written)) return [{ entity, value: plain(written) }];
    return written.map((row) => {
      const key = (row as Record<string, unknown> | null)?.[e.key];
      return { entity, ...(typeof key === "string" ? { key } : {}), value: plain(row) };
    });
  });
}

function loweringMalformed(scenario: DefinitionRef, p: LoweringViolation): Malformed {
  switch (p.kind) {
    case "unnamed":
      return {
        kind: "Malformed.unexportedDefinition",
        definition: null,
        scenario,
        data: { name: scenario.name, path: p.path },
      };
    case "lineAfterWhen":
      return { kind: "Malformed.lineAfterWhen", definition: null, scenario, data: {} };
    case "inexactTime":
      return { kind: "Malformed.inexactTime", definition: null, scenario, data: {} };
    case "misusedObserved":
      return { kind: "Malformed.misusedObserved", definition: null, scenario, data: { use: p.use, path: p.path } };
  }
}

/** The line of When that a lowering violation is at, when it is at one. */
const lineOf = (p: LoweringViolation): number | undefined =>
  p.kind === "inexactTime" || p.kind === "misusedObserved" ? p.line : undefined;

export function loadScenarios(
  root: string,
  written: readonly Named<ScenarioDefinition>[],
  services: Services,
  refOf: (definition: unknown) => DefinitionRef | undefined,
): { readonly scenarios: Named<LoadedScenario>[]; readonly malformed: Found<Malformed>[] } {
  const serviceNames = new Map([...services].map(([name, s]) => [s.definition, name]));
  const malformed: Found<Malformed>[] = [];
  const scenarios = written.map((named): Named<LoadedScenario> => {
    const { service: own, place, definition } = named;
    const ref = { service: own, name: named.name };
    const report = (violation: Malformed, at: Place = place) => malformed.push({ violation: violation, place: at });
    const entitiesOf = (service: string) => services.get(service)?.definition.entities ?? {};
    const peers: PeerEntry[] = definition.given.peers.flatMap((entry): PeerEntry[] => {
      const owner = contractService(entry.contract);
      const service = owner === undefined ? undefined : serviceNames.get(owner);
      if (service === undefined || service === own) {
        report({ kind: "Malformed.unknownPeer", definition: null, scenario: ref, data: { service: service ?? null } });
        return [];
      }
      if (entry.role === "external") return [{ service, role: "external" }];
      if (entry.role === "skip") return [{ service, role: "skip", because: entry.because }];
      return [{ service, role: "run", records: givenRecords(entitiesOf(service), entry.records) }];
    });
    if (!Number.isSafeInteger(definition.given.start))
      report({ kind: "Malformed.inexactTime", definition: null, scenario: ref, data: {} });
    const lowered = lower(definition, refOf, (contract) => {
      const owner = contractService(contract);
      return owner === undefined ? undefined : serviceNames.get(owner);
    });
    const linePlaces = lowered.stacks.map((s) => placeInStack(root, s));
    const expectationPlaces = lowered.expectationStacks.map((s) => placeInStack(root, s));
    const written = [
      [[definition.given.records, peers], place] as const,
      ...lowered.lines.map((line, i) => [line, linePlaces[i] ?? place] as const),
      ...lowered.expectations.map((e, i) => [e, expectationPlaces[i] ?? place] as const),
    ];
    for (const [value, at] of written) {
      const found = writtenKey(services, value);
      if (found !== undefined)
        report({ kind: "Malformed.writtenCreatedKey", definition: null, scenario: ref, data: found }, at);
    }
    for (const p of lowered.violations) {
      const line = lineOf(p);
      report(loweringMalformed(ref, p), (line === undefined ? undefined : linePlaces[line]) ?? place);
    }
    return {
      ...named,
      definition: {
        description: definition.description,
        scenario: {
          service: own,
          given: {
            start: definition.given.start,
            records: givenRecords(entitiesOf(own), definition.given.records),
            peers,
          },
          lines: [...lowered.lines],
          expectations: [...lowered.expectations],
        },
        linePlaces,
        expectationPlaces,
      },
    };
  });
  return { scenarios, malformed };
}
