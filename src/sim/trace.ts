import type { TraceLine } from "../data/trace.generated.ts";
import { contentOf, steps as windows } from "../data/trace.ts";
import { type Channel, sameChannel } from "../service/note.ts";
import type { StepInfo } from "../service/state.ts";

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
export function channelOf(l: TraceLine): Channel | undefined {
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
  lines: readonly TraceLine[],
  lineSteps: readonly (readonly [number, number] | undefined)[],
  a: number,
  b: number,
): boolean {
  const [channel, other] = [channelOf(lines[a] as TraceLine), channelOf(lines[b] as TraceLine)];
  if (channel === undefined || other === undefined || !sameChannel(channel, other)) return false;
  const [writerA, writerB] = [lineSteps[a], lineSteps[b]];
  return writerA === undefined || writerB === undefined || writerA[1] !== writerB[1];
}

export function snapshotLines(lines: readonly TraceLine[], causes: Causes, created: readonly string[]): TraceLine[] {
  const ls = lineSteps(lines.length, causes);
  const after = new Map<number, number[]>();
  for (const { before } of windows(lines)) {
    const window = before.map((o) => o.at - 1);
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
    if (l.dir === "out") visit(contentOf(l), i);
  });
  return lines.map((l, i) => {
    const values = created.filter((v) => firstLine.get(v) === i);
    const listed = after.get(i);
    return {
      ...l,
      ...(listed === undefined ? {} : { after: listed.map((a) => lines[a]?.id as string) }),
      ...(values.length > 0 ? { created: values } : {}),
    };
  });
}
