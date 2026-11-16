import { canonicalJson } from "../data/values.ts";
import { transitionsAt } from "./chart/basic.ts";
import { takeDeadline } from "./chart/deadline.ts";
import { applyCompletion } from "./chart/macrostep.ts";
import type { Processing } from "./chart/queue.ts";
import { type Deadline, deadlineId, machine, report } from "./state.ts";

export function fire(r: Processing, due: Deadline, step: number): void {
  const waiting = takeDeadline(r.state, due);
  r.note.readStates([[due.machine, due.state]]);
  const instance = machine(r.state, due.machine);
  if (!waiting || instance === undefined) return;
  if (instance.closed || !instance.entered.has(due.state)) return;
  applyCompletion(r, instance, transitionsAt(instance.chart, due.state, ["after", due.name, "onFired"]), {}, step);
}

const hasTime = (t: Deadline): t is Deadline & { time: Temporal.Instant } => t.time !== undefined;

/** Returns the first deadline, in entry order, due at the earliest time at or before `to`. */
export function earliestDeadline(
  deadlines: readonly Deadline[],
  to: Temporal.Instant,
): (Deadline & { time: Temporal.Instant }) | undefined {
  return deadlines.reduce<(Deadline & { time: Temporal.Instant }) | undefined>((best, t) => {
    if (!hasTime(t) || Temporal.Instant.compare(t.time, to) > 0) return best;
    return best === undefined || Temporal.Instant.compare(t.time, best.time) < 0 ? t : best;
  }, undefined);
}

/**
 * Returns the deadline that fires among `due`, the deadlines due at the earliest time in entry order, whose first is
 * `first`, in a tie: the one that the next entry of `deadlineOrder` names, or, when no entry is left, `first` unless
 * the state requires the tie order.
 */
export function chooseDeadline<T extends Deadline>(r: Processing, first: T, due: readonly T[]): T {
  const s = r.state;
  const deadlines = due.map(deadlineId);
  const [named, ...rest] = s.deadlineOrder;
  if (named === undefined) {
    if (s.tieOrderRequired)
      return report(r.state, {
        kind: "InvalidInput.unorderedDeadlines",
        definition: null,
        data: { candidates: deadlines },
      });
    return first;
  }
  const deadline = due.find((t) => canonicalJson(deadlineId(t)) === canonicalJson(named));
  if (deadline === undefined)
    return report(r.state, {
      kind: "InvalidInput.unreadyDeadline",
      definition: null,
      data: { named, candidates: deadlines },
    });
  s.deadlineOrder = rest;
  return deadline;
}
