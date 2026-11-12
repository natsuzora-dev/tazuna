import { type Problem, toProblem } from "../data/problem.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import type { MalformedLine } from "../data/trace.ts";
import { parseLines, steps } from "../data/trace.ts";
import { readTrace } from "../data/traceFile.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import type { Json } from "../data/values.ts";
import { type ViolationValue, zodError } from "../data/violation.ts";

export type Found = ViolationValue & Pick<Problem, "error">;

export const lineSchema = ({ lineNumber, issues }: MalformedLine): Found => {
  const value: Uncomparable = { kind: "Uncomparable.lineSchema", definition: null, data: { line: lineNumber } };
  return { ...value, error: zodError(issues) };
};

/**
 * Returns the JSON values and the lines of the snapshot file at `path`, undefined at blank lines, and its violations at
 * their snapshot lines: each line that the trace line schema cannot read, or, when every line is read, each unknown
 * after.
 */
export function readSnapshotProblems(path: string): {
  readonly values: readonly (Json | undefined)[];
  readonly lines: readonly (TraceLine | undefined)[];
  readonly problems: readonly Found[];
} {
  const values = readTrace(path);
  const { lines, malformed } = parseLines(values);
  return { values, lines, problems: malformed.length > 0 ? malformed.map(lineSchema) : resolveAfters(lines).unknown };
}

/**
 * Returns, for each snapshot line (1-based), the lines that its after names. An after id names the latest earlier out
 * line of the same window with the id; an id that names no such line is unknown.
 */
export function resolveAfters(snapshot: readonly (TraceLine | undefined)[]): {
  readonly follows: ReadonlyMap<number, ReadonlySet<number>>;
  readonly unknown: readonly Uncomparable[];
} {
  const follows = new Map<number, ReadonlySet<number>>();
  const unknown: Uncomparable[] = [];
  for (const { before } of steps(snapshot))
    for (const [k, { line, at }] of before.entries()) {
      const named = new Set<number>();
      for (const id of line.after ?? []) {
        const earlier = before.slice(0, k).findLast((o) => o.line.id === id);
        if (earlier === undefined)
          unknown.push({ kind: "Uncomparable.unknownAfter", definition: null, data: { line: at, id } });
        else named.add(earlier.at);
      }
      follows.set(at, named);
    }
  return { follows, unknown };
}

/** Returns each violation as a Problem at the line that its data names, or at the whole file. */
export function problemsAt(file: string, found: readonly Found[]): Problem[] {
  return found.map((v) => {
    const line = v.data["line"];
    const location = typeof line === "number" ? { file, line } : { file };
    return toProblem(v.kind, { ...v, location });
  });
}

const lineOf = (v: Found): number => {
  const line = v.data["line"];
  if (typeof line !== "number") throw new Error(`the ${v.kind} violation has no trace line`);
  return line;
};

export const byLine = (a: Found, b: Found): number => lineOf(a) - lineOf(b);
