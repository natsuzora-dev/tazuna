import { relative } from "node:path";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { Mismatch } from "../data/mismatch.generated.ts";
import { entriesOf, pair } from "../data/pairing.ts";
import type { Problem } from "../data/problem.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { jsonLine } from "../data/trace.ts";
import { parseSnapshotFile, peerSnapshotName, snapshotFolder, snapshotPath } from "../data/traceFile.ts";
import { canonicalJson, type Json } from "../data/values.ts";
import type { Spec } from "../load/load.ts";
import { problemsAt, readSnapshotProblems } from "./lines.ts";
import {
  comparedNames,
  entriesIn,
  type Folder,
  type PairingProblem,
  type PairingScenario,
  problem,
  scenarioNames,
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
  /** The compared scenarios that have a snapshot. */
  readonly compare: readonly DefinitionRef[];
  readonly problems: readonly PairingProblem[];
}

function snapshotPairing(
  scenarios: readonly PairingScenario[],
  folders: readonly Folder[],
  service: string,
): SnapshotPairing {
  const entries = entriesIn(folders, service);
  const { paired, missing, unknown } = pair(comparedNames(scenarios, service), entries);
  return {
    compare: paired.map((name) => ({ service, name })),
    problems: [
      ...missing.map((name) =>
        problem(
          { scenario: { service, name } },
          { kind: "Uncomparable.missingSnapshot", definition: null, scenario: { service, name }, data: {} },
        ),
      ),
      ...unknown.map((entry) =>
        problem(
          { service, snapshotEntry: entry },
          { kind: "Uncomparable.unknownSnapshotEntry", definition: null, data: {} },
        ),
      ),
      ...pair(scenarioNames(scenarios, service), entries).extra.map((name) =>
        problem(
          { service, snapshotEntry: `${name}.jsonl` },
          { kind: "Uncomparable.obsoleteSnapshot", definition: null, data: {} },
        ),
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
  scenarios: readonly PairingScenario[],
  folders: readonly Folder[],
): SnapshotPairing {
  const pairings = services.map((service) => snapshotPairing(scenarios, folders, service));
  return { compare: pairings.flatMap((p) => p.compare), problems: pairings.flatMap((p) => p.problems) };
}

/** Returns the service folders of the spec, and the entries of their snapshot folders. */
export function snapshotFolders(spec: Spec): {
  readonly services: readonly string[];
  readonly folders: readonly Folder[];
} {
  const services = [...new Set(spec.sources.map((s) => s.service))];
  return {
    services,
    folders: services.map((service) => ({ service, entries: entriesOf(snapshotFolder(spec, service)) })),
  };
}

/**
 * A run that can have a snapshot in the snapshot folder of `service`: a scenario's run, or, named by peerSnapshotName,
 * the run of a running peer in a scenario. `runner` is the service that
 * makes the run, whose implementation records its trace.
 */
export type SnapshotRun = DefinitionRef & { readonly runner: string };

export function snapshotRuns(spec: Spec): SnapshotRun[] {
  const peers = spec.structure.services.filter((s) => !s.external).map((s) => s.name);
  return spec.scenarios.flatMap(({ service, name }) => [
    { service, name, runner: service },
    ...peers
      .filter((peer) => peer !== service)
      .map((peer) => ({ service, name: peerSnapshotName(name, peer), runner: peer })),
  ]);
}

export function hasSnapshot(spec: Spec, runs: readonly DefinitionRef[]): (run: DefinitionRef) => boolean {
  const { services, folders } = snapshotFolders(spec);
  const { compare } = pairSnapshots(
    services,
    runs.map(({ service, name }) => ({ service, name, compared: true })),
    folders,
  );
  return (run) => compare.some((s) => sameRef(s, run));
}

export function snapshotProblems(spec: Spec, scenario: DefinitionRef, lines: readonly TraceLine[]): Problem[] {
  const path = snapshotPath(spec, scenario);
  const file = relative(spec.root, path);
  const snapshot = readSnapshotProblems(path);
  if (snapshot.problems.length > 0) return problemsAt(file, snapshot.problems, scenario);
  const mismatch = compareSnapshot(snapshot.values, lines.map(jsonLine));
  return mismatch === undefined ? [] : problemsAt(file, [mismatch], scenario);
}

/**
 * Reads the lines of a scenario's snapshot, or of a snapshot that peerSnapshots returns. Throws when the snapshot is
 * missing or has a line that is not a trace line.
 */
export function readSnapshot(spec: Spec, snapshot: DefinitionRef): TraceLine[] {
  const path = snapshotPath(spec, snapshot);
  const { lines, malformed } = parseSnapshotFile(path);
  if (malformed.length > 0)
    throw new Error(
      malformed.map((m) => `${path}:${m.lineNumber}: the line does not match the trace line schema`).join("\n"),
      { cause: malformed },
    );
  return lines;
}
