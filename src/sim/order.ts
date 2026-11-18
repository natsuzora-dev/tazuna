import type { LineId } from "../data/trace.generated.ts";
import { sameJson } from "../data/values.ts";
import type { Line, LineBody } from "../service/message.ts";
import type { StepInfo } from "../service/state.ts";

/** Lean's Channel: the channel that an `out` line travels on, seen from its sender. */
type Channel =
  | { readonly kind: "request"; readonly id: LineId }
  | { readonly kind: "answers"; readonly request: LineId }
  | { readonly kind: "events"; readonly resultOf: LineId | null };

/**
 * Lean's causedBy: whether step `later` is step `earlier` or one that it caused, a deadline step by its arming step and
 * by every step of the message whose end set its time.
 */
function causedBy(steps: readonly StepInfo[], earlier: number, later: number): boolean {
  if (later === earlier) return true;
  const timedIn = steps[later]?.timedIn;
  if (timedIn !== undefined && earlier < later && steps[earlier]?.message === timedIn) return true;
  const cause = steps[later]?.cause ?? steps[later]?.armedBy;
  return cause !== undefined && cause < later && causedBy(steps, earlier, cause);
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
