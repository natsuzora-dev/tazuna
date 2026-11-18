import type { LineId } from "../data/trace.generated.ts";
import { sameJson } from "../data/values.ts";
import type { Line, LineBody } from "../service/message.ts";
import type { StepInfo } from "../service/state.ts";

/** Lean's Channel: the channel that an `out` line travels on, seen from its sender. */
type Channel =
  | { readonly kind: "request"; readonly id: LineId }
  | { readonly kind: "answers"; readonly request: LineId }
  | { readonly kind: "events"; readonly resultOf: LineId | null };

/** Lean's causes. */
function causes(steps: readonly StepInfo[], later: number): number[] {
  const step = steps[later];
  if (step === undefined) return [];
  const direct = step.cause ?? step.armedBy;
  const { timedIn } = step;
  const timed = timedIn === undefined ? [] : steps.flatMap((s, i) => (i < later && s.message === timedIn ? [i] : []));
  return [...(direct === undefined ? [] : [direct]), ...timed];
}

/** Lean's causedBy. */
function causedBy(steps: readonly StepInfo[], earlier: number, later: number): boolean {
  return (
    later === earlier || causes(steps, later).some((c) => c < later && earlier <= c && causedBy(steps, earlier, c))
  );
}

/** Lean's LineBody.channel: the channel of the line with id `id` and body `l`, seen from its sender. */
export function channelOf(id: LineId, l: LineBody): Channel | undefined {
  switch (l.type) {
    case "command":
    case "query":
    case "subscribe":
      return { kind: "request", id };
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
 * Returns Lean's `ordered`: whether line `a` must precede line `b` among the lines of one window, because they travel
 * on one channel and `b` is caused by `a`.
 */
export function ordered(lines: readonly Line[], steps: readonly StepInfo[], a: number, b: number): boolean {
  const [la, lb] = [lines[a] as Line, lines[b] as Line];
  const [channel, other] = [channelOf(la.id, la), channelOf(lb.id, lb)];
  if (channel === undefined || other === undefined || !sameJson(channel, other)) return false;
  const [ea, eb] = [la.emitted, lb.emitted];
  if (ea === undefined || eb === undefined) return true;
  if (Temporal.Instant.compare(la.time, lb.time) < 0) return true;
  return ea.step === eb.step ? ea.group !== eb.group : causedBy(steps, ea.step, eb.step);
}

/** Lean's sentBefore: whether line `a` reaches a receiver before line `b`. */
export function sentBefore(lines: readonly Line[], steps: readonly StepInfo[], a: number, b: number): boolean {
  return a < b && (lines.slice(a + 1, b).some((l) => l.dir === "in") || ordered(lines, steps, a, b));
}

/** Lean's window: the indexes of the `out` lines of each window, between two input lines. */
export function windows(lines: readonly Line[]): number[][] {
  const result: number[][] = [[]];
  lines.forEach((l, i) => {
    if (l.dir === "out") result.at(-1)?.push(i);
    else result.push([]);
  });
  return result;
}
