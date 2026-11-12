import { readFileSync } from "node:fs";
import { join } from "node:path";
import type { DefinitionRef } from "./definitionRef.ts";
import type { TraceLine } from "./trace.generated.ts";
import { type MalformedLine, parseLines } from "./trace.ts";
import type { Json } from "./values.ts";

export const snapshotFolder = (spec: { readonly root: string }, service: string) =>
  join(spec.root, service, "__snapshots__");

export const snapshotPath = (spec: { readonly root: string }, scenario: DefinitionRef) =>
  join(snapshotFolder(spec, scenario.service), `${scenario.name}.jsonl`);

export const snapshotEntryPath = (
  spec: { readonly root: string },
  at: { readonly service: string; readonly snapshotEntry: string },
) => join(snapshotFolder(spec, at.service), at.snapshotEntry);

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
