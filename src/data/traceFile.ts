import { readFileSync } from "node:fs";
import { join } from "node:path";
import type { TraceLine } from "./trace.generated.ts";
import { type MalformedLine, parseLines } from "./trace.ts";
import type { Json } from "./values.ts";

export const snapshotFolder = (spec: { readonly root: string }, service: string) =>
  join(spec.root, service, "__snapshots__");

/**
 * A run that a snapshot records: the scenario `scenario` of `service`, made by the implementation of `runner`, which
 * is `service` for the scenario's own run and a running peer for a peer's run.
 */
export interface Run {
  readonly service: string;
  readonly scenario: string;
  readonly runner: string;
}

/** The name of a run's snapshot and trace file: the scenario's, or `<scenario>.<runner>` for a peer's run. */
export const runStem = (run: Run): string =>
  run.runner === run.service ? run.scenario : `${run.scenario}.${run.runner}`;

/** The path of a run's trace in a trace folder, and of its snapshot in the snapshot folder: `<service>/<stem>.jsonl`. */
export const runFile = (run: Run): string => join(run.service, `${runStem(run)}.jsonl`);

export const sameRun = (a: Run, b: Run): boolean =>
  a.service === b.service && a.scenario === b.scenario && a.runner === b.runner;

export const ownRun = (scenario: { readonly service: string; readonly name: string }): Run => ({
  service: scenario.service,
  scenario: scenario.name,
  runner: scenario.service,
});

export const snapshotPath = (spec: { readonly root: string }, run: Run) =>
  join(snapshotFolder(spec, run.service), `${runStem(run)}.jsonl`);

export const snapshotEntryPath = (spec: { readonly root: string }, service: string, entry: string) =>
  join(snapshotFolder(spec, service), entry);

/**
 * Returns the lines of a file, with each blank line as undefined (NDJSON skips them), so lines keep their file line
 * numbers.
 */
function linesOf(path: string): (string | undefined)[] {
  const lines = readFileSync(path, "utf8").split("\n");
  if (lines.at(-1) === "") lines.pop();
  return lines.map((l) => (l.trim() === "" ? undefined : l));
}

/** Reads the lines of a trace file. A line that is not JSON stays a string, so the line schema reports it. */
export function readTrace(path: string): (Json | undefined)[] {
  const parse = (l: string): Json => {
    try {
      return JSON.parse(l) as Json;
    } catch {
      return l;
    }
  };
  return linesOf(path).map((l) => (l === undefined ? undefined : parse(l)));
}

export function parseSnapshotFile(path: string): {
  readonly lines: TraceLine[];
  readonly malformed: readonly MalformedLine[];
} {
  const { lines, malformed } = parseLines(readTrace(path));
  return { lines: lines.filter((l) => l !== undefined), malformed };
}
