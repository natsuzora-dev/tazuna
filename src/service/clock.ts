import type { StepName } from "../data/step.generated.ts";
import { transitionsAt } from "./chart/basic.ts";
import { takeDeadline } from "./chart/deadline.ts";
import { applyCompletion } from "./chart/macrostep.ts";
import type { Processing } from "./chart/queue.ts";
import { sameStep } from "./note.ts";
import { type Deadline, machine, report } from "./state.ts";

export function fire(r: Processing, due: Deadline, step: number): void {
  const waiting = takeDeadline(r.state, due);
  r.note.readStates([[due.machine, due.state]]);
  const instance = machine(r.state, due.machine);
  if (!waiting || instance === undefined) return;
  if (instance.closed || !instance.entered.has(due.state)) return;
  applyCompletion(
    r,
    instance,
    transitionsAt(instance.chart, due.state, { type: "after", deadline: due.name }),
    {},
    step,
  );
}

/** Returns the first deadline, in entry order, due at the earliest time at or before `to`. */
export function earliestDeadline(deadlines: readonly Deadline[], to: Temporal.Instant): Deadline | undefined {
  return deadlines.reduce<Deadline | undefined>((best, t) => {
    if (Temporal.Instant.compare(t.time, to) > 0) return best;
    return best === undefined || Temporal.Instant.compare(t.time, best.time) < 0 ? t : best;
  }, undefined);
}

/** Lean's Deadline.step: the name of the step in which deadline `t` fires. */
export const deadlineStep = (t: Deadline): StepName => ({
  kind: "deadline",
  id: t.machine,
  state: t.state,
  name: t.name,
});

/**
 * Lean's chooseDeadline: returns the deadline that fires among `due`, the deadlines due at the earliest time in entry
 * order, whose first is `first`, and uses the order entry that chose it. Without a tie it is `first`. In a tie, the
 * next entry of the input's `stepOrder` chooses it, and without entries it is `first`. An entry that names an arrival is
 * for the next message of a tie of arrivals, so the tie takes `first` and keeps it.
 */
export function chooseDeadline<T extends Deadline>(r: Processing, first: T, due: readonly T[], tied: boolean): T {
  const s = r.state;
  if (!tied) return first;
  const [named, ...rest] = s.stepOrder;
  if (named === undefined || named.kind === "arrival") return first;
  const deadline = due.find((t) => sameStep(deadlineStep(t), named));
  if (deadline === undefined)
    return report(s, {
      kind: "InvalidInput.unreadyStep",
      definition: null,
      data: { named, candidates: due.map(deadlineStep) },
    });
  s.stepOrder = rest;
  return deadline;
}
