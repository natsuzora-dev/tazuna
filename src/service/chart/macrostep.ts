import type { Requester, StepName } from "../../data/step.generated.ts";
import type { Answer } from "../../data/trace.generated.ts";
import type { Fields, Json } from "../../data/values.ts";
import { automationAnswer } from "../automation.ts";
import { ref, refOf, traceNameOf } from "../basic.ts";
import { processCommand } from "../command.ts";
import { Failed, issueViolation } from "../functions.ts";
import { chartOf, type InstanceId } from "../instance.ts";
import { limits } from "../limits.ts";
import { byCallerKinds, type Emitted } from "../message.ts";
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
import { type Activity, answerTrigger, isOwn, type Transition, transitionsAt } from "./basic.ts";
import { enter, microstep } from "./microstep.ts";
import { commandWork, type Processing, type Ready, type Received, take, type Work, workLeft } from "./queue.ts";
import { sendEntered } from "./request.ts";
import { choose, leavesOf, reaches, select } from "./select.ts";

/** The event that a reaction step takes. `reactions` builds a reaction work only with events. */
function firstEvent(work: Extract<Work, { readonly kind: "reaction" }>): Emitted {
  const e = work.groups[0]?.[0];
  if (e === undefined) throw new Error("A reaction work has no event");
  return e;
}

function workName(r: Processing, work: Work): StepName {
  switch (work.kind) {
    case "reaction": {
      const e = firstEvent(work);
      return {
        kind: "reaction",
        automation: work.automation.name,
        event: refOf(r.st, work.automation.receives),
        payload: e.encoded,
      };
    }
    case "answered":
      return {
        kind: "answer",
        command: work.sent.activity.target,
        sender: work.sent.requester,
        input: work.sent.input as Json,
      };
    case "start":
      return { kind: "start", id: work.machine };
    case "receive": {
      const e = work.groups[0]?.[0];
      return e === undefined
        ? { kind: "always", id: work.machine }
        : { kind: "receive", id: work.machine, received: { key: e.key, payload: e.encoded } };
    }
    case "onDone":
      return { kind: "onDone", id: work.machine };
    case "opensDone":
      return { kind: "opensDone", id: work.machine, state: work.state, key: work.key };
  }
}

/** Lean's Ready.name. */
function readyName(r: Processing, ready: Ready): StepName {
  if (ready.kind === "work") return workName(r, ready.work);
  const { activity, requester } = ready.sent;
  return {
    kind: "command",
    command: activity.target,
    sender: requester,
    input: ready.sent.input as Json,
  };
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
function handle(r: Processing, name: InstanceId, state: string, a: Activity, answer: Answer, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  r.note.readStates([[name, state]]);
  if (instance.closed || !instance.entered.has(state)) return;
  const on = (rejected: boolean) => {
    const trigger = answerTrigger(a, rejected);
    return trigger === undefined ? [] : transitionsAt(instance.chart, state, trigger);
  };
  if (answer.result === "rejected")
    applyCompletion(r, instance, on(true), { rejection: { kind: answer.rejection.kind } }, step);
  else applyCompletion(r, instance, on(false), answer.output === undefined ? {} : { output: answer.output }, step);
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
function receiveWork(r: Processing, name: InstanceId, groups: readonly (readonly Received[])[], step: number): void {
  const e = groups[0]?.[0];
  if (e === undefined) return;
  settle(r, name, step);
  dispatch(r, name, e.key, e.payload, step);
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
  enter(r, instance, [instance.chart.initial], step);
  settle(r, name, step);
}

function showAnswer(r: Processing, name: InstanceId, slot: string, answer: Answer): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  if (answer.result === "rejected" && byCallerKinds.has(answer.rejection.kind))
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
      const reacted = r.functions.react(
        automation.name,
        event.payload,
        recordSource(r.state.records, r.note),
        r.state.now,
        nextKeys(r.state),
      );
      if (reacted instanceof Failed) halt(issueViolation(definition, reacted));
      createKeys(r.state, reacted.created);
      const input = reacted.written;
      if (input === undefined) return;
      const activity = automation.sends;
      const requester: Requester = { kind: "automation", automation: automation.name };
      if (isOwn(activity, r.st.service))
        r.queue.round.push({ order: automation.order, requester, activity, serial: undefined, input, cause: step });
      else {
        const name = traceNameOf(r.st, activity.target);
        awaitAnswer(r.state, { dir: "out", type: "command", name, input }, requester, activity);
        r.note.reached({ kind: "request", definition: activity.target, data: {} });
      }
      return;
    }
    case "answered": {
      const { sent, answer } = work;
      const live = sent.serial === undefined || takeQueued(r.state, sent.serial);
      const fault = rejectedInput(r, sent.activity.target, sent.requester, sent.input, answer);
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
  const step = newStep(r.state, undefined, { barrier: true });
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
    const next = take(r, (ready) => readyName(r, ready));
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
      const step = newStep(s, w.cause);
      const left = workLeft(w, step);
      if (left !== undefined) queue.tasks.splice(next.at, 0, left);
      inStep(r, step, workName(r, w), started(w), () => runWork(r, w, step));
      continue;
    }
    const c = next.ready.sent;
    const { step, exceeded } = newCommandStep(s, c.cause, ref(r.st, sender(c.requester)));
    if (exceeded !== undefined) report(r.state, exceeded);
    inStep(r, step, readyName(r, next.ready), undefined, () => {
      const { answer, groups } = processCommand(r, traceNameOf(r.st, c.activity.target), c.input, undefined, step);
      queue.tasks.push(...commandWork(r.st, s, groups, step), {
        kind: "answered",
        sent: c,
        answer,
        cause: step,
      });
    });
  }
}
