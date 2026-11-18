import { relative } from "node:path";
import type { Mismatch } from "../data/mismatch.generated.ts";
import { entriesOf, pair } from "../data/pairing.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { jsonLine } from "../data/trace.ts";
import { parseSnapshotFile, type Run, runStem, snapshotFolder, snapshotPath } from "../data/traceFile.ts";
import { canonicalJson, type Json } from "../data/values.ts";
import type { ReportedViolation } from "../data/violation.ts";
import type { Spec } from "../load/load.ts";
import { readSnapshotViolations, violationsAt } from "./lines.ts";
import {
  type At,
  comparedRuns,
  type Expected,
  entriesIn,
  type Folder,
  type PairingViolation,
  runsOf,
  scenarioOf,
  snapshotEntry,
  unpaired,
} from "./pairing.ts";

type LineMismatch = Extract<Mismatch, { readonly kind: "Mismatch.line" }>;

/** Returns each line that is not blank, with its file line number. */
const numbered = (snapshot: readonly (Json | undefined)[]) =>
  snapshot.flatMap((value, i) => (value === undefined ? [] : [{ line: i + 1, value }]));

/**
 * Returns the canonical text of a line, or undefined for a blank line: canonicalJson writes undefined as null, which
 * would equal a null line.
 */
const canonical = (value: Json | undefined) => (value === undefined ? undefined : canonicalJson(value));

/**
 * Compares the snapshot's lines with the run's lines as values, ignoring field order. undefined is a blank line. A line
 * missing from the snapshot is at the line after the snapshot's last.
 */
export function compareSnapshot(
  snapshot: readonly (Json | undefined)[],
  run: readonly Json[],
): LineMismatch | undefined {
  const lines = numbered(snapshot);
  for (let i = 0; i < Math.max(lines.length, run.length); i += 1)
    if (canonical(lines[i]?.value) !== canonical(run[i]))
      return {
        kind: "Mismatch.line",
        definition: null,
        line: lines[i]?.line ?? snapshot.length + 1,
        data: { snapshot: lines[i]?.value ?? null, trace: run[i] ?? null },
      };
  return undefined;
}

interface SnapshotPairing {
  /** The compared runs that have a snapshot. */
  readonly compare: readonly Run[];
  readonly violations: readonly PairingViolation<Exclude<At, { readonly kind: "traceEntry" }>>[];
}

function snapshotPairing(expected: readonly Expected[], folders: readonly Folder[], service: string): SnapshotPairing {
  const entries = entriesIn(folders, service);
  const { paired, missing, unknown } = pair(runStem, comparedRuns(expected, service), entries);
  return {
    compare: paired,
    violations: [
      ...missing.map((run) =>
        unpaired(
          { kind: "scenario", scenario: scenarioOf(run) },
          {
            kind: "Uncomparable.missingSnapshot",
            definition: null,
            scenario: scenarioOf(run),
            data: { runner: run.runner },
          },
        ),
      ),
      ...unknown.map((entry) =>
        unpaired(snapshotEntry(service, entry), {
          kind: "Uncomparable.unknownSnapshotEntry",
          definition: null,
          data: {},
        }),
      ),
      ...pair(runStem, runsOf(expected, service), entries).extra.map((name) =>
        unpaired(snapshotEntry(service, `${name}.jsonl`), {
          kind: "Uncomparable.obsoleteSnapshot",
          definition: null,
          data: {},
        }),
      ),
    ],
  };
}

/**
 * Pairs the compared scenarios of each service with their snapshots. A snapshot of a scenario that is not compared is
 * neither compared nor reported.
 */
export function pairSnapshots(
  services: readonly string[],
  expected: readonly Expected[],
  folders: readonly Folder[],
): SnapshotPairing {
  const pairings = services.map((service) => snapshotPairing(expected, folders, service));
  return { compare: pairings.flatMap((p) => p.compare), violations: pairings.flatMap((p) => p.violations) };
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
  const mismatch = compareSnapshot(snapshot.values, lines.map(jsonLine));
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
