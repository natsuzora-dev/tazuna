import { ref } from "./basic.ts";
import { settled } from "./chart/always.ts";
import { rearm } from "./chart/deadline.ts";
import { drain } from "./chart/macrostep.ts";
import type { Processing } from "./chart/queue.ts";
import { chooseDeadline, earliestDeadline, fire } from "./clock.ts";
import { Failed, issueViolation } from "./functions.ts";
import { limits } from "./limits.ts";
import { publish } from "./query.ts";
import { LazyRecordSource } from "./records.ts";
import {
  type Deadline,
  halt,
  inStep,
  NoteAccess,
  newMessage,
  newStep,
  report,
  running,
  scopeOf,
  who,
} from "./state.ts";

function checkHolds(r: Processing): void {
  for (const instance of running(r.state)) {
    if (instance.closed) continue;
    for (const state of instance.entered.keys()) {
      const scope = scopeOf(r.state, instance, state);
      const records = new LazyRecordSource(r.state.records, r.note);
      const failed = r.evaluations.quietly(() => r.functions.holds(scope, records, new NoteAccess(r, scope)));
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
    const failing = r.evaluations.quietly(() => r.functions.chartInvariant(scope, records, new NoteAccess(r, scope)));
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

/**
 * Fires the deadlines due by `to`, earliest first. A tie starts when two or more deadlines are due at the earliest
 * time; until no deadline is due at that time, the next entry of the input's `deadlineOrder` names each one that fires,
 * and after the entries, the first in entry order.
 */
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
    const deadline = tie === undefined ? e : chooseDeadline(r, e, due);
    if (Temporal.Instant.compare(deadline.time, s.now) > 0) {
      s.now = deadline.time;
      r.note.wroteNow();
    }
    newMessage(s);
    r.note.deadline(s.messageCount, deadline.time);
    const step = newStep(s, undefined);
    inStep(r, step, { kind: "deadline", who: who(s, r.st, deadline.machine), name: deadline.name }, undefined, () =>
      settled(r, deadline.machine, step, () => fire(r, deadline, step)),
    );
    drain(r);
    afterMessage(r);
  }
}

function finish(r: Processing): void {
  afterMessage(r);
  fireDue(r, r.state.now);
}

/** Processes the internal queue and finishes the message. */
export function message(r: Processing): void {
  drain(r);
  finish(r);
}
