import { join, relative } from "node:path";
import { ask } from "../cli/engine.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { InternalError } from "../data/internalError.ts";
import {
  type Expected,
  entriesOf,
  type Folder,
  type PairingViolation,
  type ScenarioAt,
  type SnapshotEntry,
  type TraceEntry,
} from "../data/pairing.ts";
import { type Run, snapshotEntryPath } from "../data/traceFile.ts";
import { type ReportedViolation, toReported } from "../data/violation.ts";
import type { Spec } from "../load/load.ts";

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

interface TracePairing {
  /** The runs whose traces verify compares with their snapshots. */
  readonly compare: readonly Run[];
  /** The traces of external services, which verify checks against their contracts. */
  readonly contract: readonly DefinitionRef[];
  readonly violations: readonly PairingViolation<TraceEntry | SnapshotEntry>[];
}

export const scenarioOf = (run: Run): DefinitionRef => ({ service: run.service, name: run.scenario });

/**
 * Pairs the compared scenarios of each service that is not external with the traces in the subfolder of the service,
 * in the engine; an external service pairs every trace name with its contract.
 */
export function pairTraces(
  services: readonly { readonly name: string; readonly external: boolean }[],
  expected: readonly Expected[],
  { others, folders }: TraceFolder,
): TracePairing {
  const [paired] = ask("pair", [{ services, expected, others, folders }]);
  if (paired === undefined) throw new InternalError("the engine gave no trace pairing");
  return {
    compare: paired.compare,
    contract: paired.contract,
    violations: paired.findings as readonly PairingViolation<TraceEntry | SnapshotEntry>[],
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
