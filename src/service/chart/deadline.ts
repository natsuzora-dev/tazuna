import { ref } from "../basic.ts";
import { Failed, issueViolation } from "../functions.ts";
import { LazyRecordSource } from "../records.ts";
import { type Deadline, halt, type Instance, NoteAccess, type State, scopeOf } from "../state.ts";
import type { Processing } from "./queue.ts";

/**
 * Lean's addDeadlines: arms the `after` deadlines of `state`, each time fixed now. A delay counts from now, and an `at`
 * is computed from current values once.
 */
export function addDeadlines(r: Processing, instance: Instance, state: string, step: number): void {
  for (const [name, deadline] of r.functions.deadlines(instance.chart.name, state)) {
    let time: Temporal.Instant | Failed;
    if (deadline.kind === "delay") time = r.state.now.add({ milliseconds: deadline.ms });
    else {
      const scope = scopeOf(r.state, instance, state);
      const records = new LazyRecordSource(r.state.records, r.note);
      time = r.functions.deadlineAt(scope, records, name, new NoteAccess(r, scope));
    }
    if (time instanceof Failed) halt(issueViolation(ref(r.st, instance.chart.name), time));
    r.state.deadlines.push({ time, machine: instance.id, state, name, armedBy: step });
  }
}

/** Removes `deadline` and returns whether it was still waiting. */
export function takeDeadline(s: State, deadline: Deadline): boolean {
  const index = s.deadlines.indexOf(deadline);
  if (index < 0) return false;
  s.deadlines.splice(index, 1);
  return true;
}
