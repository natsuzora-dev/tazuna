import { expectFound } from "../../data/internalError.ts";
import type { StateStructure } from "../../spec/structure.ts";
import { ref } from "../basic.ts";
import { Failed, issueViolation } from "../functions.ts";
import { LazyRecordSource } from "../records.ts";
import { type Deadline, halt, type Instance, NoteAccess, type State, scopeOf } from "../state.ts";
import type { Processing } from "./queue.ts";

/** Lean's addDeadlines. */
export function addDeadlines(
  r: Processing,
  instance: Instance,
  state: string,
  deadlines: StateStructure["deadlines"],
  step: number,
): void {
  for (const deadline of deadlines) {
    const { name } = deadline;
    const definition = ref(r.st, instance.chart.name);
    const data = { state, deadline: name };
    if (deadline.kind === "delay") {
      const time = r.state.now + expectFound(`delay in milliseconds of ${name}`, deadline.ms ?? undefined);
      if (!Number.isSafeInteger(time)) halt({ kind: "Fault.deadlineOutOfRange", definition, data });
      r.state.deadlines.push({ time, machine: instance.id, state, name, armedBy: step });
      continue;
    }
    const time = computedTime(r, instance, state, name);
    if (time === undefined) halt({ kind: "Fault.atSchema", definition, data });
    r.state.deadlines.push({ time, machine: instance.id, state, name, armedBy: step });
  }
}

/** Returns the instant that the deadline's `at` computes, or undefined when it computes none. */
function computedTime(r: Processing, instance: Instance, state: string, name: string): number | undefined {
  const scope = scopeOf(r.state, instance, state);
  const records = new LazyRecordSource(r.state.records, r.note);
  const computed = r.functions.deadlineAt(scope, records, name, new NoteAccess(r, scope));
  if (computed instanceof Failed) halt(issueViolation(ref(r.st, instance.chart.name), computed));
  return computed !== undefined && Number.isSafeInteger(computed) ? computed : undefined;
}

/** Removes `deadline` and returns whether it was still waiting. */
export function takeDeadline(s: State, deadline: Deadline): boolean {
  const index = s.deadlines.indexOf(deadline);
  if (index < 0) return false;
  s.deadlines.splice(index, 1);
  return true;
}
