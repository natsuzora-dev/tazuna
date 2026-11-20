import { limits } from "../../data/limits.generated.ts";
import type { Activity, Received, Requester, StepName } from "../../data/step.generated.ts";
import type { Answer } from "../../data/trace.generated.ts";
import type { Fields, Json } from "../../data/values.ts";
import { automationAnswer } from "../automation.ts";
import { ref } from "../basic.ts";
import { processCommand } from "../command.ts";
import { Failed, firstFalse, issueViolation } from "../functions.ts";
import { chartOf, type InstanceId } from "../instance.ts";
import { byCaller, type Emitted } from "../message.ts";
import { recordSource } from "../records.ts";
import { refreshScreens } from "../screen/subscription.ts";
import {
  answered,
  awaitAnswer,
  createKeys,
  halt,
  type Instance,
  inStep,
  machine,
  machineOf,
  newCommandStep,
  newStep,
  nextKeys,
  type Pending,
  rejectedInput,
  report,
  sender,
  takeQueued,
} from "../state.ts";
import { settle, settled } from "./always.ts";
import { answerTrigger, isOwn, type Transition, transitionsAt } from "./basic.ts";
import { enter, microstep } from "./microstep.ts";
import { commandWork, type Processing, type Ready, type ReceivedEvent, take, type Work, workLeft } from "./queue.ts";
import { sendEntered } from "./request.ts";
import { choose, leavesOf, reaches, select } from "./select.ts";

/** The event that a reaction step takes. `reactions` builds a reaction work only with events. */
function firstEvent(work: Extract<Work, { readonly kind: "reaction" }>): Emitted {
  const e = work.groups[0]?.[0];
  if (e === undefined) throw new Error("a reaction work has no event");
  return e;
}

function workName(work: Work): StepName {
  switch (work.kind) {
    case "reaction":
      return {
        kind: "reaction",
        automation: work.automation.name,
        event: work.automation.receives,
        payload: work.groups[0]?.[0]?.encoded ?? null,
        delivered: work.delivered.map((g) => g.map((e) => e.encoded)),
      };
    case "answered": {
      const { activity, requester, input } = work.sent;
      return { kind: "answer", activity, sender: requester, input: input as Json, answer: work.answer as Json };
    }
    case "start":
      return { kind: "start", id: work.machine };
    case "receive": {
      const e = work.groups[0]?.[0];
      const received = ({ key, payload }: ReceivedEvent): Received => ({ key, payload });
      return e === undefined
        ? { kind: "always", id: work.machine }
        : {
            kind: "receive",
            id: work.machine,
            received: received(e),
            delivered: work.delivered.map((g) => g.map(received)),
          };
    }
    case "onDone":
      return { kind: "onDone", id: work.machine };
    case "opensDone":
      return { kind: "opensDone", id: work.machine, state: work.state, key: work.key };
  }
}

/** Lean's Ready.name. */
function readyName(ready: Ready): StepName {
  if (ready.kind === "work") return workName(ready.work);
  const { activity, requester, input } = ready.sent;
  return { kind: "command", activity, sender: requester, input: input as Json };
}

function started(work: Work): InstanceId | undefined {
  return work.kind === "start" ? work.machine : undefined;
}

export function applyCompletion(
  r: Processing,
  instance: Instance,
  transitions: readonly Transition[],
  extra: Fields,
  step: number,
): void {
  const t = choose(r, instance, transitions, extra);
  if (t === undefined) return;
  microstep(r, instance, [{ instance, t }], extra, step);
}

/** Handles an answer with the transitions of the state's activity that sent the request. */
/** Lean's Instance.answerTransitions: the transitions of `instance` at `state` that take `answer` to activity `a`. */
function answerTransitions(instance: Instance, state: string, a: Activity, answer: Answer): readonly Transition[] {
  const trigger = answerTrigger(a, answer.result === "rejected");
  return trigger === undefined ? [] : transitionsAt(instance.chart, state, trigger);
}

function handle(r: Processing, name: InstanceId, state: string, a: Activity, answer: Answer, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  r.note.readStates([[name, state]]);
  if (instance.closed || !instance.entered.has(state)) return;
  const ts = answerTransitions(instance, state, a, answer);
  if (answer.result === "rejected")
    applyCompletion(r, instance, ts, { rejection: { kind: answer.rejection.kind } }, step);
  else applyCompletion(r, instance, ts, answer.output === undefined ? {} : { output: answer.output }, step);
}

export function dispatch(r: Processing, name: InstanceId, key: string, payload: unknown, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined || instance.closed) return;
  const extra = { payload };
  const leaves = leavesOf(r, instance, (copy) => reaches(r, copy, payload), { type: "on", key });
  const chosen = select(r, instance, { type: "on", key }, extra, leaves);
  if (chosen.length === 0) return;
  microstep(r, instance, chosen, extra, step);
}

/** Lean's receiveWork: processes the first event of the work; without one it only settles. */
function receiveWork(
  r: Processing,
  name: InstanceId,
  groups: readonly (readonly ReceivedEvent[])[],
  step: number,
): void {
  const e = groups[0]?.[0];
  if (e === undefined) return;
  settle(r, name, step);
  dispatch(r, name, e.key, e.decoded, step);
}

function done(r: Processing, name: InstanceId, n: string, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  r.note.readStates([[instance.id, n]]);
  if (instance.closed || !instance.entered.has(n)) return;
  applyCompletion(r, instance, transitionsAt(instance.chart, n, { type: "onDone" }), {}, step);
}

/** Takes the onDone transitions of the finished states, including the states that finish during this work. */
function doneWork(r: Processing, name: InstanceId, step: number): void {
  for (let selections = 0; ; selections += 1) {
    const instance = machine(r.state, name);
    if (instance === undefined) return;
    const [n, ...rest] = instance.awaitingOnDone ?? [];
    if (n === undefined) {
      instance.awaitingOnDone = undefined;
      return;
    }
    if (selections === limits.onDoneSelections)
      report(r.state, {
        kind: "Fault.exceededOnDoneSelections",
        definition: ref(r.st, instance.chart.name),
        data: { limit: limits.onDoneSelections },
      });
    instance.awaitingOnDone = rest;
    settle(r, name, step);
    done(r, name, n, step);
  }
}

function startWork(r: Processing, name: InstanceId, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  instance.startStep = step;
  enter(r, instance, [instance.chart.initial], step);
  settle(r, name, step);
}

function showAnswer(r: Processing, name: InstanceId, slot: string, answer: Answer): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  if (answer.result === "rejected" && byCaller.has(answer.rejection.kind))
    report(r.state, {
      kind: "Fault.rejectedShows",
      definition: ref(r.st, chartOf(name)),
      data: { slot, rejection: answer.rejection },
    });
  if (answer.result !== "fulfilled") return;
  r.note.wroteShown(instance.id, slot);
  instance.shown.set(slot, answer.output);
}

function answerTo(r: Processing, step: number, activity: Activity, answer: Answer, requester: Requester): void {
  switch (requester.kind) {
    case "automation":
      automationAnswer(r, requester.automation, answer);
      return;
    case "state":
      handle(r, requester.machine, requester.state, activity, answer, step);
      return;
    case "slot":
      showAnswer(r, requester.machine, requester.slot, answer);
      return;
  }
}

export function deliverAnswer(r: Processing, step: number, p: Pending, answer: Answer): void {
  const live = answered(r.state, p);
  if (live) answerTo(r, step, p.activity, answer, p.requester);
}

function settledMachine(work: Work): InstanceId | undefined {
  switch (work.kind) {
    case "receive":
    case "onDone":
    case "opensDone":
      return work.machine;
    case "answered":
      return machineOf(work.sent.requester);
    case "start":
    case "reaction":
      return undefined;
  }
}

function workBody(r: Processing, work: Work, step: number): void {
  switch (work.kind) {
    case "reaction": {
      const { automation } = work;
      const event = firstEvent(work);
      const definition = ref(r.st, automation.name);
      r.note.reached({ kind: "automation", definition, data: {} });
      const records = recordSource(r.state.records, r.note);
      const { now } = r.state;
      const unbound = firstFalse((binding) => {
        const bound = r.functions.automationBinding(automation.name, binding, event.payload, records, now);
        if (bound instanceof Failed) return bound;
        const kind = bound ? "automationBindingValue" : "automationBindingNull";
        r.note.reached({ kind, definition, data: { binding } });
        return bound;
      }, automation.binds);
      if (unbound instanceof Failed) halt(issueViolation(definition, unbound));
      if (unbound !== undefined) return;
      const failing = firstFalse((condition) => {
        const met = r.functions.automationGuard(automation.name, condition, event.payload, records, now);
        if (met instanceof Failed) return met;
        r.note.reached({ kind: "automationGuard", definition, data: { condition, met } });
        return met;
      }, automation.guard);
      if (failing instanceof Failed) halt(issueViolation(definition, failing));
      if (failing !== undefined) return;
      const reacted = r.functions.react(automation.name, event.payload, records, now, nextKeys(r.state));
      if (reacted instanceof Failed) halt(issueViolation(definition, reacted));
      createKeys(r.state, reacted.created);
      const input = reacted.written;
      const activity = automation.sends;
      const requester: Requester = { kind: "automation", automation: automation.name };
      if (isOwn(activity, r.st.service))
        r.queue.round.push({ order: automation.order, requester, activity, serial: undefined, input, cause: step });
      else {
        awaitAnswer(r.state, { type: "command", target: activity.target, input }, requester, activity);
        r.note.reached({ kind: "request", definition: activity.target, data: {} });
      }
      return;
    }
    case "answered": {
      const { sent, answer } = work;
      // Whether the Queued is stale depends on whether the machine left the sending state, which matters only when the
      // answer has a transition to take.
      if (sent.requester.kind === "state") {
        const { machine: name, state } = sent.requester;
        const instance = machine(r.state, name);
        if (instance !== undefined && answerTransitions(instance, state, sent.activity, answer).length > 0)
          r.note.readStates([[name, state]]);
      }
      const live = sent.serial === undefined || takeQueued(r.state, sent.serial);
      const fault = rejectedInput(r, sent.activity.target, sender(sent.requester), sent.input, answer);
      if (fault !== undefined) {
        report(r.state, fault);
        return;
      }
      if (live) answerTo(r, step, sent.activity, answer, sent.requester);
      return;
    }
    case "start":
      startWork(r, work.machine, step);
      return;
    case "receive":
      receiveWork(r, work.machine, work.groups, step);
      return;
    case "onDone":
      doneWork(r, work.machine, step);
      return;
    case "opensDone": {
      const { state, key, output, serial } = work;
      const live = takeQueued(r.state, serial);
      r.note.readStates([[work.machine, state]]);
      const instance = machine(r.state, work.machine);
      if (!live || instance === undefined) return;
      applyCompletion(r, instance, transitionsAt(instance.chart, state, { type: "opens", key }), { output }, step);
      return;
    }
  }
}

function runWork(r: Processing, work: Work, step: number): void {
  settled(r, settledMachine(work), step, () => workBody(r, work, step));
}

function settleScreen(r: Processing, name: InstanceId): void {
  const step = newStep(r.state, { kind: "root" }, { barrier: true });
  inStep(r, step, { kind: "always", id: name }, undefined, () => settle(r, name, step));
}

/**
 * Processes the internal queue of one message to completion, in the order of W3C SCXML Appendix D. The internal queue
 * first processes the work that steps cause. Whenever work runs out, the commands sent to the own service in the
 * meantime (a round) join the command queue in sender-definition order and run one by one. When both are empty (the end
 * of the macrostep), sendEntered sends the activities of the entered states, and the work and commands that they cause
 * run. No cause orders the work and commands that wait at one time, so the input's `stepOrder` may take any of them
 * first (take).
 */
export function drain(r: Processing): void {
  const { state: s, queue } = r;
  let messageWork = 0;
  const countWork = () => {
    if (messageWork === limits.messageWork)
      report(r.state, { kind: "Fault.exceededMessageWork", definition: null, data: { limit: limits.messageWork } });
    messageWork += 1;
  };
  for (;;) {
    const next = take(r, readyName);
    if (next === undefined) {
      if (queue.entered.length > 0) {
        countWork();
        sendEntered(r);
        continue;
      }
      const screens = refreshScreens(r);
      if (screens.length === 0) return;
      countWork();
      for (const screen of screens) settleScreen(r, screen);
      continue;
    }
    countWork();
    if (next.ready.kind === "work") {
      const w = next.ready.work;
      const step = newStep(s, w.cause === undefined ? { kind: "root" } : { kind: "caused", cause: w.cause });
      const left = workLeft(w, step);
      if (left !== undefined) queue.tasks.splice(next.at, 0, left);
      inStep(r, step, workName(w), started(w), () => runWork(r, w, step));
      continue;
    }
    const c = next.ready.sent;
    const { step, exceeded } = newCommandStep(s, c.cause, ref(r.st, sender(c.requester)));
    if (exceeded !== undefined) report(r.state, exceeded);
    inStep(r, step, readyName(next.ready), undefined, () => {
      const { answer, groups } = processCommand(r, c.activity.target.name, c.input, undefined, step);
      queue.tasks.push(...commandWork(r.st, s, groups, step), {
        kind: "answered",
        sent: c,
        answer,
        cause: step,
      });
    });
  }
}
