import { ref } from "../basic.ts";
import { Failed, issueViolation } from "../functions.ts";
import { LazyRecordSource } from "../records.ts";
import { type Deadline, halt, type Instance, NoteAccess, type State, scopeOf } from "../state.ts";
import type { Processing } from "./queue.ts";

/**
 * Lean's instantTime?: the instant that `text` writes, when renderTime writes it back as `text`. parseTime reads a
 * four-digit year, and renderTime writes whole milliseconds.
 */
function instantTime(text: string): Temporal.Instant | undefined {
  if (!/^\d{4}-/.test(text)) return undefined;
  const instant = Temporal.Instant.from(text);
  return instant.epochNanoseconds % 1_000_000n === 0n && instant.toString() === text ? instant : undefined;
}

/** Lean's addDeadlines: arms the `after` deadlines of `state`, each time fixed now (deadlineTime). */
export function addDeadlines(r: Processing, instance: Instance, state: string, step: number): void {
  for (const name of r.functions.deadlines(instance.chart.name, state)) {
    const scope = scopeOf(r.state, instance, state);
    const records = new LazyRecordSource(r.state.records, r.note);
    const definition = ref(r.st, instance.chart.name);
    const computed = r.functions.deadlineTime(scope, records, name, new NoteAccess(r, scope));
    if (computed instanceof Failed) halt(issueViolation(definition, computed));
    const time = computed === undefined ? undefined : instantTime(computed);
    if (time === undefined) halt({ kind: "Fault.atSchema", definition, data: { state, deadline: name } });
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
