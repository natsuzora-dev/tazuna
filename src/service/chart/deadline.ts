import { ref } from "../basic.ts";
import { type DeadlineTime, Failed, issueViolation } from "../functions.ts";
import type { InstanceId } from "../instance.ts";
import { LazyRecordSource } from "../records.ts";
import { type Deadline, halt, machine, NoteAccess, type Run, type State, scopeOf } from "../state.ts";

export function addDeadlines(
  s: State,
  resource: InstanceId,
  state: string,
  deadlines: readonly (readonly [string, DeadlineTime])[],
): void {
  for (const [name, deadline] of deadlines)
    s.deadlines.push({
      time: deadline.kind === "delay" ? s.now.add({ milliseconds: deadline.ms }) : undefined,
      fromAt: deadline.kind === "atExpression",
      machine: resource,
      state,
      name,
    });
}

export function rearm(r: Run): void {
  for (const deadline of r.state.deadlines) {
    const instance = machine(r.state, deadline.machine);
    if (!deadline.fromAt || instance === undefined) continue;
    const scope = scopeOf(r.state, instance, deadline.state);
    const records = new LazyRecordSource(r.state.records, r.note);
    const time = r.functions.deadlineAt(scope, records, deadline.name, new NoteAccess(r, scope));
    if (time instanceof Failed) halt(issueViolation(ref(r.st, instance.chart.name), time));
    deadline.time = time;
  }
}

/** Removes `deadline` and returns whether it was still waiting. */
export function takeDeadline(s: State, deadline: Deadline): boolean {
  const index = s.deadlines.indexOf(deadline);
  if (index < 0) return false;
  s.deadlines.splice(index, 1);
  return true;
}
