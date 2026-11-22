import type { z } from "zod";
import { type TraceLine, traceLine } from "./trace.generated.ts";
import { type Json, plain } from "./values.ts";

/** A trace line before its writer adds the time. */
export type UntimedTraceLine = TraceLine extends infer L ? (L extends TraceLine ? Omit<L, "time"> : never) : never;

/** The sender that a trace line id written by lineIdText names, when it is a received message's id. */
export function senderOf(id: string): string | undefined {
  const parts = id.split("/");
  return parts.length === 2 ? parts[0] : undefined;
}

/** Pairs of a snapshot string and the trace string that stands for it. */
export type Bindings = ReadonlyMap<string, string>;

/** Returns the line as JSON whose keys start with time, dir, type, and id, in that order. */
export const jsonLine = ({ time, dir, type, id, ...rest }: TraceLine): Json => plain({ time, dir, type, id, ...rest });

export const toJsonl = (lines: readonly TraceLine[]): string =>
  `${lines.map((l) => JSON.stringify(jsonLine(l))).join("\n")}\n`;

/** A line the trace line schema cannot read; `lineNumber` is 1-based. */
export interface MalformedLine {
  readonly lineNumber: number;
  readonly issues: readonly z.core.$ZodIssue[];
}

/** A line of a trace file; undefined is a blank line. */
export type FileLine = TraceLine | MalformedLine | undefined;

export const isMalformed = (l: FileLine): l is MalformedLine => l !== undefined && "issues" in l;

/** A line of an implementation's trace: test writes `after` and `created` only in a snapshot. */
const implementationLine = traceLine.superRefine((line, ctx) => {
  for (const key of ["after", "created"] as const)
    if (key in line) ctx.addIssue({ code: "custom", path: [key], message: `only a snapshot line has ${key}` });
});

function parseWith(schema: typeof traceLine, values: readonly unknown[]): FileLine[] {
  return values.map((value, i) => {
    if (value === undefined) return undefined;
    const line = schema.safeParse(plain(value));
    return line.success ? line.data : { lineNumber: i + 1, issues: line.error.issues };
  });
}

/** Parses the lines of an implementation's trace. */
export const parseFileLines = (values: readonly unknown[]): FileLine[] => parseWith(implementationLine, values);

/** Returns the lines of a snapshot, with each MalformedLine as undefined in `lines`, and the malformed lines. */
export function parseLines(values: readonly unknown[]): {
  lines: (TraceLine | undefined)[];
  malformed: MalformedLine[];
} {
  const read = parseWith(traceLine, values);
  return { lines: read.map((l) => (isMalformed(l) ? undefined : l)), malformed: read.filter(isMalformed) };
}
