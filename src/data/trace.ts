import type { z } from "zod";
import type { Subject } from "./mismatch.generated.ts";
import { type TraceLine, traceLine } from "./trace.generated.ts";
import { type Json, plain } from "./values.ts";

/** A trace line before its writer adds the time. */
export type UntimedTraceLine = TraceLine extends infer L ? (L extends TraceLine ? Omit<L, "time"> : never) : never;

export function contentOf(line: TraceLine): unknown {
  switch (line.type) {
    case "command":
    case "query":
    case "subscribe":
      return line.input;
    case "event":
    case "operation":
      return line.payload;
    case "answer":
      return line.answer;
    case "unsubscribe":
    case "time":
    case "restart":
      return undefined;
  }
}

/** Returns whether two lines have the same instant; the +09:00 and Z spellings of one instant are equal. */
export const sameTime = (a: TraceLine, b: TraceLine): boolean =>
  Temporal.Instant.compare(Temporal.Instant.from(a.time), Temporal.Instant.from(b.time)) === 0;

export const nameOf = (l: TraceLine): string | undefined => ("name" in l ? l.name : undefined);

export const toOf = (l: TraceLine): string | undefined => ("to" in l ? l.to : undefined);

/** Lean's Subject.of. */
export const subjectOf = (l: TraceLine): Subject =>
  l.type === "answer" || l.type === "unsubscribe"
    ? { type: l.type, to: l.to }
    : { type: l.type, name: nameOf(l) ?? null, id: l.id };

export const resultOf = (l: TraceLine): string | undefined => ("resultOf" in l ? l.resultOf : undefined);

/**
 * Lean's receivedId: the id by which the receiver of a message from `sender` names it in its trace. `sentId` and
 * `senderOf` read it back; together they are the one place a simulated message's id meets a string.
 */
export const receivedId = (sender: string, id: string): string => `${sender}/${id}`;

/** Lean's sentId?: the sender's id of a message that `service` received with the id `id`, when `service` sent it. */
export const sentId = (service: string, id: string): string | undefined =>
  id.startsWith(`${service}/`) ? id.slice(service.length + 1) : undefined;

/** Lean's senderOf?: the service whose message `id` names, when another service sent it. */
export function senderOf(id: string): string | undefined {
  const parts = id.split("/");
  return parts.length === 2 ? parts[0] : undefined;
}

/** Lean's operationName: the name of an operation line, the one place that joins a screen and its control. */
export const operationName = (screen: string, control: string): string => `${screen}.${control}`;

/** Lean's operationParts: the screen and the control that the name of an operation line joins. */
export function operationParts(name: string): { readonly screen: string; readonly control: string } {
  const [screen = "", control = ""] = name.split(".");
  return { screen, control };
}

export interface NumberedLine {
  readonly line: TraceLine;
  /** The 1-based line number. */
  readonly at: number;
}

/** The lines of a trace, grouped by the input that follows them; the last step's outputs have no input after them. */
export type Steps = readonly { readonly before: readonly NumberedLine[]; readonly input: NumberedLine | undefined }[];

export function steps(lines: readonly (TraceLine | undefined)[]): Steps {
  const result: { before: NumberedLine[]; input: NumberedLine | undefined }[] = [{ before: [], input: undefined }];
  lines.forEach((line, i) => {
    if (line === undefined) return;
    const last = result.at(-1) as { before: NumberedLine[]; input: NumberedLine | undefined };
    if (line.dir === "out") last.before.push({ line, at: i + 1 });
    else {
      last.input = { line, at: i + 1 };
      result.push({ before: [], input: undefined });
    }
  });
  return result;
}

/** Pairs of a snapshot string and the trace string that stands for it. */
export type Bindings = ReadonlyMap<string, string>;

/** Returns `value` with each string that `bindings` binds replaced by its bound value. */
export const substituted = (bindings: Bindings, value: Json): Json => {
  if (typeof value === "string") return bindings.get(value) ?? value;
  if (Array.isArray(value)) return value.map((v: Json) => substituted(bindings, v));
  if (value !== null && typeof value === "object")
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, substituted(bindings, v)]));
  return value;
};

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

export function parseFileLines(values: readonly unknown[]): FileLine[] {
  return values.map((value, i) => {
    if (value === undefined) return undefined;
    const line = traceLine.safeParse(plain(value));
    return line.success ? line.data : { lineNumber: i + 1, issues: line.error.issues };
  });
}

/** Returns the lines of parseFileLines, with each MalformedLine as undefined in `lines`, and the malformed lines. */
export function parseLines(values: readonly unknown[]): {
  lines: (TraceLine | undefined)[];
  malformed: MalformedLine[];
} {
  const read = parseFileLines(values);
  return { lines: read.map((l) => (isMalformed(l) ? undefined : l)), malformed: read.filter(isMalformed) };
}

/** Returns the lines before the first malformed line, and that line. */
export function untilMalformed(lines: readonly FileLine[]): {
  lines: (TraceLine | undefined)[];
  malformed: MalformedLine | undefined;
} {
  const read: (TraceLine | undefined)[] = [];
  for (const l of lines) {
    if (isMalformed(l)) return { lines: read, malformed: l };
    read.push(l);
  }
  return { lines: read, malformed: undefined };
}
