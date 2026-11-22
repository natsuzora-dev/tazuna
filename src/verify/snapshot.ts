import { relative } from "node:path";
import { ask } from "../cli/engine.ts";
import { InternalError } from "../data/internalError.ts";
import {
  type Expected,
  entriesOf,
  type Folder,
  type PairingViolation,
  type ScenarioAt,
  type SnapshotEntry,
} from "../data/pairing.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { jsonLine } from "../data/trace.ts";
import { parseSnapshotFile, type Run, snapshotFolder, snapshotPath } from "../data/traceFile.ts";
import type { ReportedViolation } from "../data/violation.ts";
import type { Spec } from "../load/load.ts";
import { readSnapshotViolations, violationsAt } from "./lines.ts";
import { scenarioOf } from "./pairing.ts";

/**
 * Pairs the compared scenarios of each service with their snapshots, in the engine. A snapshot of a scenario that is
 * not compared is neither compared nor reported.
 */
export function pairSnapshots(
  services: readonly string[],
  expected: readonly Expected[],
  folders: readonly Folder[],
): { readonly compare: readonly Run[]; readonly violations: readonly PairingViolation<ScenarioAt | SnapshotEntry>[] } {
  const [paired] = ask("pairSnapshots", [{ services, expected, folders }]);
  if (paired === undefined) throw new InternalError("the engine gave no snapshot pairing");
  return {
    compare: paired.compare,
    violations: paired.findings as readonly PairingViolation<ScenarioAt | SnapshotEntry>[],
  };
}

/** Returns the services of the spec, and the entries of their snapshot folders. */
export function snapshotFolders(spec: Spec): {
  readonly services: readonly string[];
  readonly folders: readonly Folder[];
} {
  const services = [...spec.services.keys()];
  return {
    services,
    folders: services.map((service) => ({ service, entries: entriesOf(snapshotFolder(spec, service)) })),
  };
}

/** Returns every run that can have a snapshot: each scenario's own run, and the run of each other spec service in it. */
export function snapshotRuns(spec: Spec): Run[] {
  const runners = spec.structure.services.filter((s) => !s.external).map((s) => s.name);
  return spec.scenarios.flatMap(({ service, name }) => [
    { service, scenario: name, runner: service },
    ...runners.filter((r) => r !== service).map((runner) => ({ service, scenario: name, runner })),
  ]);
}

/** Returns the runs among `runs` that have a snapshot. */
export function withSnapshot(spec: Spec, runs: readonly Run[]): Run[] {
  const { services, folders } = snapshotFolders(spec);
  return [
    ...pairSnapshots(
      services,
      runs.map((run) => ({ run, compared: true })),
      folders,
    ).compare,
  ];
}

export function snapshotViolations(spec: Spec, run: Run, lines: readonly TraceLine[]): ReportedViolation[] {
  const path = snapshotPath(spec, run);
  const file = relative(spec.root, path);
  const snapshot = readSnapshotViolations(path);
  if (snapshot.violations.length > 0) return violationsAt(file, snapshot.violations, scenarioOf(run));
  const [compared] = ask("compareSnapshot", [
    { snapshot: snapshot.values.map((v) => v ?? null), run: lines.map(jsonLine) },
  ]);
  const mismatch = compared?.mismatch ?? undefined;
  return mismatch === undefined ? [] : violationsAt(file, [mismatch], scenarioOf(run));
}

/** Reads the lines of a run's snapshot. Throws when the snapshot is missing or has a line that is not a trace line. */
export function readSnapshot(spec: Spec, run: Run): TraceLine[] {
  const path = snapshotPath(spec, run);
  const { lines, malformed } = parseSnapshotFile(path);
  if (malformed.length > 0)
    throw new Error(
      malformed.map((m) => `${path}:${m.lineNumber}: the line does not match the trace line schema`).join("\n"),
      { cause: malformed },
    );
  return lines;
}
