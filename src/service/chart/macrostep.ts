import type { StepName } from "../../data/choiceDependent.generated.ts";
import type { Answer } from "../../data/trace.generated.ts";
import type { Fields } from "../../data/values.ts";
import { withExtra } from "../../data/violation.ts";
import { automationAnswer } from "../automation.ts";
import { ref, refOf } from "../basic.ts";
import { processCommand } from "../command.ts";
import { Failed, issueViolation } from "../functions.ts";
import { limits } from "../limits.ts";
import { byCallerKinds } from "../message.ts";
import { recordSource } from "../records.ts";
import { refreshScreens } from "../screen/subscription.ts";
import {
  answered,
  awaitAnswer,
  awaitedActivities,
  chartName,
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
  type Requester,
  repeatedKeyCall,
  report,
  sender,
  senderOf,
  takeQueued,
  who,
} from "../state.ts";
import { settle, settled } from "./always.ts";
import { type Activity, activityRef, type Transition, transitionsAt } from "./basic.ts";
import { enter, microstep } from "./microstep.ts";
import { commandWork, type Processing, type Ready, take, type Work } from "./queue.ts";
import { sendEntered } from "./request.ts";
import { choose, leavesOf, reaches, select } from "./select.ts";

function workName(r: Processing, work: Work): StepName {
  switch (work.kind) {
    case "reaction":
      return { kind: "reaction", automation: ref(r.st, work.automation.name) };
    case "answered":
      return {
        kind: "answer",
        command: refOf(r.st, work.sent.activity.target),
        sender: who(r.state, r.st, sender(work.sent.requester)),
      };
    case "start":
      return { kind: "start", who: who(r.state, r.st, work.machine) };
    case "receive":
      return work.received.length === 0
        ? { kind: "always", who: who(r.state, r.st, work.machine) }
        : {
            kind: "receive",
            who: who(r.state, r.st, work.machine),
            keys: work.received.map((received) => received.key),
          };
    case "onDone":
      return { kind: "onDone", who: who(r.state, r.st, work.machine) };
    case "opensDone":
      return { kind: "opensDone", who: who(r.state, r.st, work.machine), key: work.key };
  }
}

/** Lean's State.readyName. */
function readyName(r: Processing, ready: Ready): StepName {
  if (ready.kind === "work") return workName(r, ready.work);
  const { activity, requester } = ready.sent;
  return { kind: "command", command: refOf(r.st, activity.target), sender: who(r.state, r.st, sender(requester)) };
}

function startedResource(work: Work): string | undefined {
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
function handle(r: Processing, name: string, state: string, a: Activity, answer: Answer, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  r.note.readStates([[name, state]]);
  if (instance.closed || !instance.entered.has(state)) return;
  const at = (outcome: string) => transitionsAt(instance.chart, state, [a.keyword, a.key, outcome]);
  const success = a.keyword === "calls" ? "onFulfilled" : "onAccepted";
  if (answer.result === "rejected")
    applyCompletion(r, instance, at("onRejected"), { rejection: { kind: answer.rejection.kind } }, step);
  else applyCompletion(r, instance, at(success), answer.output === undefined ? {} : { output: answer.output }, step);
}

export function dispatch(r: Processing, name: string, key: string, payload: unknown, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined || instance.closed) return;
  const extra = { payload };
  const leaves = leavesOf(r, instance, (copy) => reaches(r, copy, payload), ["on", key]);
  const chosen = select(r, instance, ["on", key], extra, leaves);
  if (chosen.length === 0) return;
  microstep(r, instance, chosen, extra, step);
}

function receiveWork(
  r: Processing,
  name: string,
  received: readonly { key: string; payload: unknown }[],
  step: number,
): void {
  for (const { key, payload } of received) {
    settle(r, name, step);
    dispatch(r, name, key, payload, step);
  }
}

function done(r: Processing, name: string, n: string, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  r.note.readStates([[instance.resource, n]]);
  if (instance.closed || !instance.entered.has(n)) return;
  applyCompletion(r, instance, transitionsAt(instance.chart, n, ["onDone"]), {}, step);
}

/** Takes the onDone transitions of the finished states, including the states that finish during this work. */
function doneWork(r: Processing, name: string, step: number): void {
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

function startWork(r: Processing, name: string, step: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  enter(r, instance, [instance.chart.initial], step);
  settle(r, name, step);
}

function showAnswer(r: Processing, name: string, slot: string, answer: Answer): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  if (answer.result === "rejected" && byCallerKinds.has(answer.rejection.kind))
    report(r.state, {
      kind: "Fault.rejectedShows",
      definition: ref(r.st, chartName(r.state, name)),
      data: { slot, rejection: answer.rejection },
    });
  if (answer.result !== "fulfilled") return;
  r.note.wroteShown(instance.resource, slot);
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

function settledMachine(work: Work): string | undefined {
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
      const { automation, event } = work;
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
      const repeated = repeatedKeyCall(r.state, reacted.created);
      if (repeated !== undefined)
        halt({ kind: "Fault.repeatedKeyLabel", definition, data: { entity: repeated.entity, label: repeated.label } });
      createKeys(r.state, reacted.created);
      if (reacted.input === undefined) return;
      const activity = automation.sends;
      const requester: Requester = { kind: "automation", automation: automation.name };
      const normalized = r.functions.normalize({ kind: "input", definition: activityRef(activity) }, reacted.input);
      if (normalized instanceof Failed) halt(issueViolation(definition, normalized));
      if ("error" in normalized)
        report(
          r.state,
          withExtra({ kind: "Fault.automationInputSchema", definition, data: {} }, { error: normalized.error }),
        );
      const input = normalized.encoded;
      if (activity.own)
        r.queue.round.push({ order: automation.order, requester, activity, serial: undefined, input, cause: step });
      else {
        r.note.requested(activity, senderOf(r.state, requester), awaitedActivities(r.state));
        awaitAnswer(
          r.state,
          { dir: "out", type: "command", name: activity.target, input },
          requester,
          activity,
          normalized.value,
        );
        r.note.reached({ kind: "request", definition: activityRef(activity), data: {} });
      }
      return;
    }
    case "answered": {
      const { sent, answer } = work;
      const live = sent.serial === undefined || takeQueued(r.state, sent.serial);
      if (live) answerTo(r, step, sent.activity, answer, sent.requester);
      return;
    }
    case "start":
      startWork(r, work.machine, step);
      return;
    case "receive":
      receiveWork(r, work.machine, work.received, step);
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
      applyCompletion(r, instance, transitionsAt(instance.chart, state, ["opens", key, "onDone"]), { output }, step);
      return;
    }
  }
}

function runWork(r: Processing, work: Work, step: number): void {
  settled(r, settledMachine(work), step, () => workBody(r, work, step));
}

function settleScreen(r: Processing, name: string): void {
  const step = newStep(r.state, undefined, { barrier: true });
  inStep(r, step, { kind: "always", who: who(r.state, r.st, name) }, undefined, () => settle(r, name, step));
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
    if (next.kind === "work") {
      const w = next.work;
      const step = newStep(s, w.cause);
      inStep(r, step, workName(r, w), startedResource(w), () => runWork(r, w, step));
      continue;
    }
    const c = next.sent;
    const { step, exceeded } = newCommandStep(s, c.cause, ref(r.st, senderOf(s, c.requester)));
    if (exceeded !== undefined) report(r.state, exceeded);
    inStep(r, step, readyName(r, next), undefined, () => {
      const { answer, emits } = processCommand(r, c.activity.target, c.input, undefined, step);
      queue.tasks.push(...commandWork(r.st, s, emits, step), {
        kind: "answered",
        sent: c,
        answer,
        cause: step,
      });
    });
  }
}
