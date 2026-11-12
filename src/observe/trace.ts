import type { TraceLine } from "../data/trace.generated.ts";
import { contentOf, sameTime, steps as windows } from "../data/trace.ts";
import type { StepInfo } from "../semantics/state.ts";

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

/**
 * The causes of trace lines. `events` holds the step, first line, and line count of each step that wrote event lines,
 * and `deadlines` holds the message number and time of each deadline message.
 */
export interface Causes {
  readonly events: (readonly [number, number, number])[];
  readonly deadlines: (readonly [number, Temporal.Instant])[];
}

/** Returns, for each line, the step that wrote it if it is an event line. */
function lineSteps(lineCount: number, causes: Causes): (number | undefined)[] {
  const steps: (number | undefined)[] = Array.from({ length: lineCount }, () => undefined);
  for (const [step, start, count] of causes.events) steps.fill(step, start, start + count);
  return steps;
}

/** Returns, for each message (numbered from 1), the deadline time if it is a deadline message. */
function messages(messageCount: number, causes: Causes): (Temporal.Instant | undefined)[] {
  return Array.from({ length: messageCount }, (_, k) => causes.deadlines.find(([message]) => message === k + 1)?.[1]);
}

/**
 * Returns Lean's `raceScopeOf messages k` for each message number k (from 0). Consecutive deadline messages at the same
 * time share a race scope.
 */
function raceScopes(messages: readonly (Temporal.Instant | undefined)[]): number[] {
  const scopes = [0];
  let previous: Temporal.Instant | undefined;
  for (const time of messages) {
    const scope = scopes.at(-1) as number;
    scopes.push(time !== undefined && previous !== undefined && time.equals(previous) ? scope : scope + 1);
    previous = time;
  }
  return scopes;
}

/**
 * Returns whether line `a` is ordered before line `b`. Only event lines are ordered, because an implementation keeps
 * order only within the events that a service emits.
 */
function ordered(
  lines: readonly TraceLine[],
  steps: readonly StepInfo[],
  lineSteps: readonly (number | undefined)[],
  scopes: readonly number[],
  a: number,
  b: number,
): boolean {
  const [stepA, stepB] = [lineSteps[a], lineSteps[b]];
  if (stepA === undefined || stepB === undefined) return false;
  if (lines[a]?.type !== "event" || lines[b]?.type !== "event") return false;
  const [earlier, later] = [steps[stepA], steps[stepB]];
  if (earlier === undefined || later === undefined) return false;
  if (scopes[earlier.message] !== scopes[later.message]) return earlier.message < later.message;
  return leadsTo(steps, stepA, stepB);
}

export function snapshotLines(
  lines: readonly TraceLine[],
  steps: readonly StepInfo[],
  messageCount: number,
  causes: Causes,
  created: readonly string[],
): TraceLine[] {
  const ls = lineSteps(lines.length, causes);
  const scopes = raceScopes(messages(messageCount, causes));
  const after = new Map<number, number[]>();
  for (const { before } of windows(lines)) {
    const window = before.map((o) => o.at - 1);
    for (const b of window) {
      const earlier = window.filter(
        (a) =>
          a < b && (ordered(lines, steps, ls, scopes, a, b) || !sameTime(lines[a] as TraceLine, lines[b] as TraceLine)),
      );
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
