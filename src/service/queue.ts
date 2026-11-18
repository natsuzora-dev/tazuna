import { limits } from "../data/limits.generated.ts";
import { ref } from "./basic.ts";
import { settled } from "./chart/always.ts";
import { rearm } from "./chart/deadline.ts";
import { drain } from "./chart/macrostep.ts";
import type { Processing } from "./chart/queue.ts";
import { chooseDeadline, deadlineStep, earliestDeadline, fire } from "./clock.ts";
import { Failed, issueViolation } from "./functions.ts";
import { publish } from "./query.ts";
import { LazyRecordSource } from "./records.ts";
import { type Deadline, halt, inStep, NoteAccess, newMessage, newStep, report, running, scopeOf } from "./state.ts";

function checkHolds(r: Processing): void {
  for (const instance of running(r.state)) {
    if (instance.closed) continue;
    for (const state of instance.entered.keys()) {
      const scope = scopeOf(r.state, instance, state);
      const records = new LazyRecordSource(r.state.records, r.note);
      const failed = r.functions.holds(scope, records, new NoteAccess(r, scope));
      if (failed !== undefined) halt(issueViolation(ref(r.st, instance.chart.name), failed));
    }
  }
}

function checkInvariants(r: Processing): void {
  for (const instance of r.state.machines.values()) {
    if (instance.closed) continue;
    const definition = ref(r.st, instance.chart.name);
    const scope = scopeOf(r.state, instance, null);
    const records = new LazyRecordSource(r.state.records, r.note);
    const failing = r.functions.chartInvariant(scope, records, new NoteAccess(r, scope));
    if (failing instanceof Failed) halt(issueViolation(definition, failing));
    if (failing) report(r.state, { kind: "Fault.failedChartInvariant", definition, data: { condition: failing } });
  }
}

function afterMessage(r: Processing): void {
  checkHolds(r);
  checkInvariants(r);
  rearm(r);
  publish(r);
}

/** Lean's endMessage: afterMessage, noted as the end of the current message. */
function endMessage(r: Processing): void {
  r.note.afterMessageBegins(r.state.messageCount);
  try {
    afterMessage(r);
  } finally {
    r.note.afterMessageEnds();
  }
}

/** Lean's fireDue: fires the deadlines due by `to`, each tie chosen by chooseDeadline. */
export function fireDue(r: Processing, to: Temporal.Instant): void {
  const s = r.state;
  let fired = 0;
  let tie: Temporal.Instant | undefined;
  for (let e = earliestDeadline(s.deadlines, to); e !== undefined; e = earliestDeadline(s.deadlines, to)) {
    if (fired === limits.dueDeadlines)
      report(s, { kind: "Fault.exceededDueDeadlines", definition: null, data: { limit: limits.dueDeadlines } });
    fired += 1;
    const { time } = e;
    const due = s.deadlines.filter((t): t is Deadline & { time: Temporal.Instant } => t.time?.equals(time) === true);
    tie = due.length > 1 || tie?.equals(time) === true ? time : undefined;
    const deadline = chooseDeadline(r, e, due, tie !== undefined);
    if (Temporal.Instant.compare(deadline.time, s.now) > 0) {
      s.now = deadline.time;
      r.note.wroteNow();
    }
    newMessage(s);
    const step = newStep(s, undefined, {
      tie: tie === undefined ? undefined : { kind: "deadlines", time: tie },
      armedBy: deadline.armedBy,
    });
    inStep(r, step, deadlineStep(deadline), undefined, () =>
      settled(r, deadline.machine, step, () => fire(r, deadline, step)),
    );
    drain(r);
    endMessage(r);
  }
}

function finish(r: Processing): void {
  endMessage(r);
  fireDue(r, r.state.now);
}

/** Processes the internal queue and finishes the message. */
export function message(r: Processing): void {
  drain(r);
  finish(r);
}
