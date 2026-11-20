import { join, relative } from "node:path";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { InternalError } from "../data/internalError.ts";
import { type Entry, entriesOf, pair } from "../data/pairing.ts";
import { type Run, runStem, snapshotEntryPath } from "../data/traceFile.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import { type ReportedViolation, toReported } from "../data/violation.ts";
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

type TraceEntry = { readonly kind: "traceEntry"; readonly service?: string; readonly entry: string };
type SnapshotEntry = { readonly kind: "snapshotEntry"; readonly service: string; readonly entry: string };
type ScenarioAt = { readonly kind: "scenario"; readonly scenario: DefinitionRef };

/** An entry of the trace folder or of its subfolder `service`, an entry of the snapshot folder of `service`, or a scenario. */
export type At = TraceEntry | SnapshotEntry | ScenarioAt;

export interface PairingViolation<A extends At = At> {
  readonly at: A;
  readonly violation: Uncomparable;
}

interface TracePairing {
  /** The runs whose traces verify compares with their snapshots. */
  readonly compare: readonly Run[];
  /** The traces of external services, which verify checks against their contracts. */
  readonly contract: readonly DefinitionRef[];
  readonly violations: readonly PairingViolation<TraceEntry | SnapshotEntry>[];
}

export interface Expected {
  readonly run: Run;
  /**
   * Whether the run is compared. A compared run's file is compared when present and reported when missing; the file of
   * a run that is not compared is ignored.
   */
  readonly compared: boolean;
}

export const unpaired = <A extends At>(at: A, violation: Uncomparable): PairingViolation<A> => ({ at, violation });

const traceEntry = (service: string | undefined, entry: string): TraceEntry => ({
  kind: "traceEntry",
  ...(service === undefined ? {} : { service }),
  entry,
});

export const snapshotEntry = (service: string, entry: string): SnapshotEntry => ({
  kind: "snapshotEntry",
  service,
  entry,
});

const unknownTraceEntry = (at: TraceEntry) =>
  unpaired(at, { kind: "Uncomparable.unknownTraceEntry", definition: null, data: {} });

export const entriesIn = (folders: readonly Folder[], service: string): readonly Entry[] =>
  folders.find((f) => f.service === service)?.entries ?? [];

export const runsOf = (expected: readonly Expected[], service: string): Run[] =>
  expected.filter((s) => s.run.service === service).map((s) => s.run);

export const comparedRuns = (expected: readonly Expected[], service: string): Run[] =>
  expected.filter((s) => s.run.service === service && s.compared).map((s) => s.run);

export const scenarioOf = (run: Run): DefinitionRef => ({ service: run.service, name: run.scenario });

/** Returns the violations of the subfolder of a service that is not a service of the spec. */
function unknownServiceViolations({ service, entries }: Folder): PairingViolation<TraceEntry>[] {
  const { extra, unknown } = pair((n: string) => n, [], entries);
  return [
    ...extra.map((name) =>
      unpaired(traceEntry(service, `${name}.jsonl`), {
        kind: "Uncomparable.unknownService",
        definition: null,
        data: { service },
      }),
    ),
    ...unknown.map((entry) => unknownTraceEntry(traceEntry(service, entry))),
  ];
}

/**
 * Pairs a service's compared scenarios with its traces; an external service pairs every trace name with its contract.
 */
function servicePairing(
  expected: readonly Expected[],
  folders: readonly Folder[],
  { name: service, external }: { readonly name: string; readonly external: boolean },
): TracePairing {
  const entries = entriesIn(folders, service);
  const { paired, missing, extra, unknown } = pair(runStem, external ? [] : comparedRuns(expected, service), entries);
  const unknownEntries = unknown.map((entry) => unknownTraceEntry(traceEntry(service, entry)));
  if (external) return { compare: [], contract: extra.map((name) => ({ service, name })), violations: unknownEntries };
  return {
    compare: paired,
    contract: [],
    violations: [
      ...unknownEntries,
      ...pair(runStem, runsOf(expected, service), entries).extra.map((name) =>
        unpaired(traceEntry(service, `${name}.jsonl`), {
          kind: "Uncomparable.unknownScenario",
          definition: null,
          scenario: { service, name },
          data: {},
        }),
      ),
      ...missing.map((run) =>
        unpaired(snapshotEntry(service, `${runStem(run)}.jsonl`), {
          kind: "Uncomparable.missingTrace",
          definition: null,
          scenario: scenarioOf(run),
          data: { runner: run.runner },
        }),
      ),
    ],
  };
}

/**
 * Pairs the compared scenarios of each service that is not external with the traces in the subfolder of the service.
 */
export function pairTraces(
  services: readonly { readonly name: string; readonly external: boolean }[],
  expected: readonly Expected[],
  { others, folders }: TraceFolder,
): TracePairing {
  const pairings = services.map((s) => servicePairing(expected, folders, s));
  return {
    compare: pairings.flatMap((p) => p.compare),
    contract: pairings.flatMap((p) => p.contract),
    violations: [
      ...others.map((entry) => unknownTraceEntry(traceEntry(undefined, entry))),
      ...folders.filter((f) => !services.some((s) => s.name === f.service)).flatMap(unknownServiceViolations),
      ...pairings.flatMap((p) => p.violations),
    ],
  };
}

const snapshotEntryAt = (spec: Spec, at: SnapshotEntry) =>
  ({ file: relative(spec.root, snapshotEntryPath(spec, at.service, at.entry)) }) as const;

/** Returns a violation of pairing traces with snapshots at its place in the trace folder `traces` or a snapshot folder. */
export function tracePairingViolation(
  spec: Spec,
  { at, violation }: PairingViolation<TraceEntry | SnapshotEntry>,
  traces: string,
): ReportedViolation {
  if (at.kind === "snapshotEntry") return toReported(violation, snapshotEntryAt(spec, at));
  return toReported(violation, { file: relative(spec.root, join(traces, at.service ?? "", at.entry)) });
}

/** Returns a violation of pairing runs with snapshots at its place: a scenario, or an entry of a snapshot folder. */
export function snapshotPairingViolation(
  spec: Spec,
  { at, violation }: PairingViolation<ScenarioAt | SnapshotEntry>,
): ReportedViolation {
  if (at.kind === "snapshotEntry") return toReported(violation, snapshotEntryAt(spec, at));
  const scenario = spec.scenarios.find((s) => s.service === at.scenario.service && s.name === at.scenario.name);
  if (scenario === undefined) throw new InternalError(`no scenario ${at.scenario.service}.${at.scenario.name}`);
  return toReported(violation, scenario.place);
}
