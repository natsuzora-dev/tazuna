import { join, relative } from "node:path";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { type Entry, entriesOf, pair } from "../data/pairing.ts";
import { type Problem, toProblem } from "../data/problem.ts";
import { snapshotEntryPath } from "../data/traceFile.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import type { Spec } from "../load/load.ts";

/** The subfolder `service` of the trace folder, or the snapshot folder of `service`. */
export interface Folder {
  readonly service: string;
  readonly entries: readonly Entry[];
}

/** The entries of a trace folder: the subfolders as `folders`, each other entry as `others`. */
export interface TraceFolder {
  readonly others: readonly string[];
  readonly folders: readonly Folder[];
}

export function traceFolderOf(folder: string): TraceFolder {
  const top = entriesOf(folder);
  return {
    others: top.filter((e) => e.kind !== "folder").map((e) => e.name),
    folders: top
      .filter((e) => e.kind === "folder")
      .map((e) => ({ service: e.name, entries: entriesOf(join(folder, e.name)) })),
  };
}

/**
 * An entry of the trace folder or of its subfolder `service`, an entry of the snapshot folder of `service`, or a
 * scenario.
 */
export type At =
  | { readonly service?: string; readonly entry: string }
  | { readonly service: string; readonly snapshotEntry: string }
  | { readonly scenario: DefinitionRef };

export interface PairingProblem {
  readonly at: At;
  readonly violation: Uncomparable;
}

interface TracePairing {
  /** The traces that verify compares with their snapshots. */
  readonly compare: readonly DefinitionRef[];
  /** The traces of external services, which verify checks against their contracts. */
  readonly contract: readonly DefinitionRef[];
  readonly problems: readonly PairingProblem[];
}

export type PairingScenario = DefinitionRef & {
  /**
   * Whether the scenario is compared. A compared scenario's file is compared when present and reported when missing;
   * the file of a scenario that is not compared is ignored.
   */
  readonly compared: boolean;
};

export const problem = (at: At, violation: Uncomparable): PairingProblem => ({ at, violation });

const unknownTraceEntry = (at: At) =>
  problem(at, { kind: "Uncomparable.unknownTraceEntry", definition: null, data: {} });

export const entriesIn = (folders: readonly Folder[], service: string): readonly Entry[] =>
  folders.find((f) => f.service === service)?.entries ?? [];

export const scenarioNames = (scenarios: readonly PairingScenario[], service: string): string[] =>
  scenarios.filter((s) => s.service === service).map((s) => s.name);

export const comparedNames = (scenarios: readonly PairingScenario[], service: string): string[] =>
  scenarios.filter((s) => s.service === service && s.compared).map((s) => s.name);

/** Returns the violations of the subfolder of a service that is not a service of the spec. */
function unknownServiceViolations({ service, entries }: Folder): PairingProblem[] {
  const { extra, unknown } = pair([], entries);
  return [
    ...extra.map((name) =>
      problem(
        { service, entry: `${name}.jsonl` },
        { kind: "Uncomparable.unknownService", definition: null, data: { service } },
      ),
    ),
    ...unknown.map((entry) => unknownTraceEntry({ service, entry })),
  ];
}

/**
 * Pairs a service's compared scenarios with its traces; an external service pairs every trace name with its contract.
 */
function servicePairing(
  scenarios: readonly PairingScenario[],
  folders: readonly Folder[],
  { name: service, external }: { readonly name: string; readonly external: boolean },
): TracePairing {
  const entries = entriesIn(folders, service);
  const { paired, missing, extra, unknown } = pair(external ? [] : comparedNames(scenarios, service), entries);
  const unknownEntries = unknown.map((entry) => unknownTraceEntry({ service, entry }));
  if (external) return { compare: [], contract: extra.map((name) => ({ service, name })), problems: unknownEntries };
  return {
    compare: paired.map((name) => ({ service, name })),
    contract: [],
    problems: [
      ...unknownEntries,
      ...pair(scenarioNames(scenarios, service), entries).extra.map((name) =>
        problem(
          { service, entry: `${name}.jsonl` },
          { kind: "Uncomparable.unknownScenario", definition: null, data: { scenario: { service, name } } },
        ),
      ),
      ...missing.map((name) =>
        problem(
          { service, snapshotEntry: `${name}.jsonl` },
          { kind: "Uncomparable.missingTrace", definition: { service, name }, data: {} },
        ),
      ),
    ],
  };
}

/**
 * Pairs the compared scenarios of each service that is not external with the traces in the subfolder of the service.
 */
export function pairTraces(
  services: readonly { readonly name: string; readonly external: boolean }[],
  scenarios: readonly PairingScenario[],
  { others, folders }: TraceFolder,
): TracePairing {
  const pairings = services.map((s) => servicePairing(scenarios, folders, s));
  return {
    compare: pairings.flatMap((p) => p.compare),
    contract: pairings.flatMap((p) => p.contract),
    problems: [
      ...others.map((entry) => unknownTraceEntry({ entry })),
      ...folders.filter((f) => !services.some((s) => s.name === f.service)).flatMap(unknownServiceViolations),
      ...pairings.flatMap((p) => p.problems),
    ],
  };
}

/**
 * Returns the violation of a pairing at its place. `traces` is the trace folder, which holds the places of trace folder
 * entries.
 */
export function pairingProblem(spec: Spec, { at, violation }: PairingProblem, traces?: string): Problem {
  if ("scenario" in at) {
    const scenario = spec.scenarios.find((s) => sameRef(s, at.scenario));
    if (scenario === undefined) throw new Error(`no scenario ${at.scenario.service}.${at.scenario.name}`);
    return toProblem(violation.kind, { ...violation, location: scenario.place });
  }
  if ("snapshotEntry" in at)
    return toProblem(violation.kind, {
      ...violation,
      location: { file: relative(spec.root, snapshotEntryPath(spec, at)) },
    });
  if (traces === undefined) throw new Error(`the trace folder entry ${at.entry} has no trace folder`);
  const path = join(traces, at.service ?? "", at.entry);
  return toProblem(violation.kind, { ...violation, location: { file: relative(spec.root, path) } });
}
