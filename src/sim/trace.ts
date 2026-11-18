import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Channel } from "../data/note.generated.ts";
import type { LineId, TraceLine } from "../data/trace.generated.ts";
import { lineIdText, operationName } from "../data/trace.ts";
import { sameJson } from "../data/values.ts";
import { bodyContent, type Line } from "../service/message.ts";
import type { StepInfo } from "../service/state.ts";
import { traceNameOfRef } from "../spec/structure.ts";

/**
 * Returns whether step `earlier` comes before step `later` through the cause chain or through a barrier of the same
 * message.
 */
export function leadsTo(steps: readonly StepInfo[], earlier: number, later: number): boolean {
  if (later === earlier) return true;
  const first = steps[earlier];
  const last = steps[later];
  if (earlier < later && first?.barrier === true && first.message === last?.message) return true;
  if (last === undefined) return false;
  if (last.barrier && earlier < later && first?.message === last.message) return true;
  return last.cause !== undefined && last.cause < later && leadsTo(steps, earlier, last.cause);
}

/** The causes of trace lines: the step, first line, and line count of each group of event lines that a step wrote. */
export interface Causes {
  readonly events: (readonly [number, number, number])[];
}

/** Returns, for each line, the step that wrote it and the number of its group if it is an event line. */
export function lineSteps(lineCount: number, causes: Causes): (readonly [number, number] | undefined)[] {
  const steps: (readonly [number, number] | undefined)[] = Array.from({ length: lineCount }, () => undefined);
  causes.events.forEach(([step, start, count], group) => {
    steps.fill([step, group], start, start + count);
  });
  return steps;
}

/** Lean's channelOf: the channel that an `out` line travels on, seen from its sender. */
export function channelOf(l: Line): Channel | undefined {
  switch (l.type) {
    case "command":
    case "query":
    case "subscribe":
      return { kind: "request", id: l.id };
    case "unsubscribe":
      return { kind: "request", id: l.to };
    case "answer":
      return { kind: "answers", request: l.to };
    case "event":
      return { kind: "events", resultOf: l.resultOf ?? null };
    default:
      return undefined;
  }
}

/**
 * Returns Lean's `ordered`: whether line `a` must precede line `b`, because they travel on one channel and are not two
 * lines of one group of events.
 */
function ordered(
  lines: readonly Line[],
  lineSteps: readonly (readonly [number, number] | undefined)[],
  a: number,
  b: number,
): boolean {
  const [channel, other] = [channelOf(lines[a] as Line), channelOf(lines[b] as Line)];
  if (channel === undefined || other === undefined || !sameJson(channel, other)) return false;
  const [writerA, writerB] = [lineSteps[a], lineSteps[b]];
  return writerA === undefined || writerB === undefined || writerA[1] !== writerB[1];
}

/** Lean's window: the indexes of the `out` lines of each window, between two input lines. */
function windows(lines: readonly Line[]): number[][] {
  const result: number[][] = [[]];
  lines.forEach((l, i) => {
    if (l.dir === "out") result.at(-1)?.push(i);
    else result.push([]);
  });
  return result;
}

/**
 * Lean's traceLineOf: the trace line of `line` of the trace of `service`, with its `after` and `created`. This is where
 * a definition gets its trace name and a line id its text.
 */
export function traceLineOf(
  service: string,
  line: Line,
  after: readonly LineId[] = [],
  created: readonly string[] = [],
): TraceLine {
  const extra = {
    ...(after.length > 0 ? { after: after.map(lineIdText) } : {}),
    ...(created.length > 0 ? { created: [...created] } : {}),
  };
  const { time, dir } = line;
  const id = lineIdText(line.id);
  const name = (r: DefinitionRef) => traceNameOfRef(r, service);
  switch (line.type) {
    case "command":
    case "query":
    case "subscribe":
      return { time, dir, type: line.type, id, name: name(line.target), input: line.input, ...extra };
    case "event":
      return {
        time,
        dir,
        type: "event",
        id,
        name: name(line.event),
        payload: line.payload,
        ...(line.resultOf === undefined ? {} : { resultOf: lineIdText(line.resultOf) }),
        ...extra,
      };
    case "answer":
      return { time, dir, type: "answer", id, to: lineIdText(line.to), answer: line.answer, ...extra };
    case "unsubscribe":
      return { time, dir, type: "unsubscribe", id, to: lineIdText(line.to), ...extra };
    case "time":
    case "restart":
      return { time, dir: "in", type: line.type, id, ...extra };
    case "operation":
      return {
        time,
        dir,
        type: "operation",
        id,
        name: operationName(name(line.screen), line.control),
        ...(line.nth === undefined ? {} : { nth: line.nth }),
        ...("payload" in line ? { payload: line.payload } : {}),
        ...extra,
      };
  }
}

/** The trace lines of `lines` of the trace of `service` as its snapshot holds them, with `after` and `created`. */
export function snapshotLines(
  service: string,
  lines: readonly Line[],
  causes: Causes,
  created: readonly string[],
): TraceLine[] {
  const ls = lineSteps(lines.length, causes);
  const after = new Map<number, number[]>();
  for (const window of windows(lines)) {
    for (const b of window) {
      const earlier = window.filter((a) => a < b && ordered(lines, ls, a, b));
      if (earlier.length > 0) after.set(b, earlier);
    }
  }
  const firstLine = new Map<string, number>();
  const visit = (value: unknown, i: number): void => {
    if (typeof value === "string") {
      if (created.includes(value) && !firstLine.has(value)) firstLine.set(value, i);
    } else if (value && typeof value === "object") for (const v of Object.values(value)) visit(v, i);
  };
  lines.forEach((l, i) => {
    if (l.dir === "out") visit(bodyContent(l), i);
  });
  return lines.map((l, i) =>
    traceLineOf(
      service,
      l,
      (after.get(i) ?? []).map((a) => (lines[a] as Line).id),
      created.filter((v) => firstLine.get(v) === i),
    ),
  );
}
