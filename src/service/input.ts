import type { DefinitionRef } from "../data/definitionRef.ts";
import type { InvalidInput } from "../data/invalidInput.generated.ts";
import type { Answer, LineId } from "../data/trace.generated.ts";
import { lineIdText } from "../data/trace.ts";
import type { Json } from "../data/values.ts";
import { withExtra } from "../data/violation.ts";
import {
  assumptionMismatch,
  assumptionViolation,
  hasOutput,
  isAssumed,
  rejectionKinds,
  rejectionReasons,
  requiresOf,
  resultOfMismatch,
} from "../spec/structure.ts";
import { ref, type Service } from "./basic.ts";
import { settled } from "./chart/always.ts";
import type { Chart } from "./chart/basic.ts";
import { deliverAnswer, dispatch } from "./chart/macrostep.ts";
import { commandWork, type Processing, reactions, type Work } from "./chart/queue.ts";
import { initialContextOf, newInstance } from "./chart/request.ts";
import { processCommand } from "./command.ts";
import { firstFalse } from "./contract.ts";
import { Failed, issueViolation } from "./functions.ts";
import { answerAgain, keep, type Request } from "./idempotency.ts";
import { chartOf, type InstanceId, topId } from "./instance.ts";
import { type Emitted, idKey, sameLineId } from "./message.ts";
import { resolveChecked } from "./query.ts";
import { message } from "./queue.ts";
import { accepting } from "./screen/operable.ts";
import {
  type Finding,
  halt,
  inputFault,
  machineOf,
  newMessage,
  newStep,
  nthOpen,
  type Outgoing,
  type Pending,
  type Run,
  rejectedInput,
  report,
  write,
} from "./state.ts";

/** Whether `target` is an own definition named in `names`. */
const owns = (st: Service, names: readonly string[], target: DefinitionRef): boolean =>
  target.service === st.service && names.includes(target.name);

export function send(r: Processing, target: DefinitionRef, input: unknown, given: { readonly id?: LineId }): void {
  const s = r.state;
  if (!owns(r.st, r.st.commands, target)) unownedTarget(r, target);
  const name = target.name;
  const request: Request = { name, input };
  const id = write(s, { dir: "in", type: "command", ...given, target, input });
  newMessage(s);
  const step = newStep(s, undefined);
  const known = s.commandAnswers.get(idKey(id));
  if (known === undefined) {
    const { answer, groups } = processCommand(r, name, input, id, step);
    r.queue.tasks.push(...commandWork(r.st, s, groups, step));
    keep(s.commandAnswers, id, request, answer);
  } else write(s, { dir: "out", type: "answer", to: id, answer: answerAgain(known, request) });
  message(r);
}

function unownedTarget(r: Processing, target: DefinitionRef): never {
  return report(r.state, { kind: "InvalidInput.unownedTarget", definition: null, data: { target } });
}

export function call(r: Processing, target: DefinitionRef, input: unknown, given: { readonly id?: LineId }): void {
  const s = r.state;
  if (!owns(r.st, r.st.queries, target)) unownedTarget(r, target);
  const id = write(s, { dir: "in", type: "query", ...given, target, input });
  newMessage(s);
  write(s, { dir: "out", type: "answer", to: id, answer: resolveChecked(r, target.name, input) });
  message(r);
}

export function subscribe(r: Processing, target: DefinitionRef, input: unknown, given: { readonly id?: LineId }): void {
  const s = r.state;
  if (!owns(r.st, r.st.queries, target)) unownedTarget(r, target);
  const id = write(s, { dir: "in", type: "subscribe", ...given, target, input });
  if (!s.subscriptions.subscribe(id, { query: target.name, input }))
    report(r.state, {
      kind: "InvalidInput.reusedSubscriptionId",
      definition: null,
      data: { subscriptionId: lineIdText(id) },
    });
  newMessage(s);
  message(r);
}

/** Lean's endSubscription: the unsubscribe input that ends the subscription `id`. */
export function endSubscription(r: Processing, id: LineId): void {
  const s = r.state;
  write(s, { dir: "in", type: "unsubscribe", to: id });
  if (!s.subscriptions.unsubscribe(id))
    report(r.state, {
      kind: "InvalidInput.unopenedSubscription",
      definition: null,
      data: { subscriptionId: lineIdText(id) },
    });
  newMessage(s);
  message(r);
}

/** Lean's resultRequest: the request `handle` whose answer arrived, which an event names as its resultOf. */
function resultRequest(r: Processing, event: DefinitionRef, handle: LineId): LineId | undefined {
  const outgoing = r.state.outgoing.get(idKey(handle));
  if (outgoing?.answer === undefined)
    return report(r.state, {
      kind: "InvalidInput.resultOfUnansweredRequest",
      definition: null,
      data: { event, requestId: lineIdText(handle) },
    });
  const target = outgoing.activity.target;
  const mismatch = resultOfMismatch(r.st.structure, target, outgoing.answer.result === "accepted", event);
  if (mismatch === undefined) return handle;
  return report(r.state, {
    kind: `InvalidInput.${mismatch}`,
    definition: null,
    data: { event, requestId: lineIdText(handle), target },
  });
}

/** Lean's checkResults. */
export function checkResults(r: Run): void {
  for (const { id, activity, accepted } of r.state.outgoing.values()) {
    if (accepted === undefined) continue;
    const target = activity.target;
    const failed = r.functions.resultEnsures(target, accepted.input, accepted.output, accepted.events);
    if (failed instanceof Failed) halt(issueViolation(target, failed));
    if (failed !== undefined)
      report(
        r.state,
        assumptionViolation(
          "InvalidInput",
          { requestId: lineIdText(id), target },
          { kind: "failedAssumedEnsures", condition: failed },
        ),
      );
  }
}

/** Lean's redeliver. */
function redeliver(r: Processing, event: DefinitionRef, payload: unknown, id: LineId, resultOf?: LineId): void {
  const s = r.state;
  const request = resultOf === undefined ? undefined : resultRequest(r, event, resultOf);
  write(s, {
    dir: "in",
    type: "event",
    id,
    event,
    payload,
    ...(request === undefined ? {} : { resultOf: request }),
  });
  newMessage(s);
  message(r);
}

export function receive(r: Processing, event: DefinitionRef, payload: unknown, id: LineId, resultOf?: LineId): void {
  const s = r.state;
  if (s.deliveries.has(idKey(id))) {
    redeliver(r, event, payload, id, resultOf);
    return;
  }
  const parsed = r.functions.parse({ kind: "payload", event }, payload);
  if (parsed instanceof Failed) halt(issueViolation(event, parsed));
  if ("error" in parsed)
    report(
      s,
      withExtra(
        { kind: "InvalidInput.eventPayloadSchema", definition: null, data: { event } },
        { error: parsed.error },
      ),
    );
  const decoded = parsed.value;
  const request = resultOf === undefined ? undefined : resultRequest(r, event, resultOf);
  write(s, {
    dir: "in",
    type: "event",
    id,
    event,
    payload,
    ...(request === undefined ? {} : { resultOf: request }),
  });
  s.deliveries.add(idKey(id));
  const e: Emitted = { event, payload: decoded, encoded: parsed.encoded as Json };
  if (request !== undefined) s.outgoing.get(idKey(request))?.accepted?.events.push(e);
  newMessage(s);
  const step = newStep(s, undefined);
  r.queue.tasks.push(...reactions(r.st, s, [[e]], false, step));
  message(r);
}

/** Returns the assumption that an answer to the request `requestId` to `target` breaks (assumptionMismatch). */
function brokenAssumption(
  requestId: LineId,
  target: DefinitionRef,
  answer: Answer,
  failedRequires: string | undefined,
  failedEnsures: string | undefined,
): InvalidInput | undefined {
  const m = assumptionMismatch(answer, failedRequires, failedEnsures);
  return m === undefined
    ? undefined
    : assumptionViolation("InvalidInput", { requestId: lineIdText(requestId), target }, m);
}

interface AnswerCheck {
  /** The assumption that the answer breaks, reported without halting. */
  readonly assumption?: InvalidInput | undefined;
  /** The answer to deliver, decoded, or why it is malformed or the sender's fault. */
  readonly checked: { readonly decoded: Answer } | { readonly violation: Finding };
  /** An assumed peer's acceptance of a command, whose ensures the end of the run checks with its result events. */
  readonly accepted?: Outgoing["accepted"];
}

/** Lean's decodedAnswer: the answer decoded, or why its rejection kind or output does not match the target. */
function decodedAnswer(r: Processing, p: Pending, answer: Answer): AnswerCheck["checked"] {
  const target = p.activity.target;
  const request = { requestId: lineIdText(p.id), target };
  const structure = r.st.structure;
  if (answer.result === "rejected") {
    const { rejection } = answer;
    if (!rejectionKinds(structure, r.st.service, target).includes(rejection.kind))
      return {
        violation: assumptionViolation("InvalidInput", request, { kind: "unlistedRejectionKind", rejection }),
      };
    if (rejection.kind === "requires" && !rejectionReasons(structure, target).includes(rejection.reason ?? ""))
      return {
        violation: { kind: "InvalidInput.unlistedRejectionReason", definition: null, data: { ...request, rejection } },
      };
    return { decoded: answer };
  }
  if (!hasOutput(structure, target)) return { decoded: answer };
  const parsed = r.functions.parse({ kind: "output", definition: target }, answer.output);
  if (parsed instanceof Failed) return halt(issueViolation(target, parsed));
  if ("error" in parsed)
    return {
      violation: withExtra(assumptionViolation("InvalidInput", request, { kind: "answerOutputSchema" }), {
        error: parsed.error,
      }),
    };
  return { decoded: { ...answer, output: parsed.value } as Answer };
}

/** Lean's specAnswer: the check of an answer from a spec service, which parsed the input itself. */
function specAnswer(r: Processing, p: Pending, answer: Answer): AnswerCheck {
  const fault = rejectedInput(r, p.activity.target, p.requester, p.input, answer);
  return { checked: fault === undefined ? decodedAnswer(r, p, answer) : { violation: fault } };
}

/**
 * Lean's assumedAnswer: the check of an answer from an assumed peer. Its input schema stands for the peer's parse, and
 * the answer is also checked against its requires over the input alone and, for a query, its ensures that read no
 * records; a command's ensures waits for the end of the run, when all its result events arrived.
 */
function assumedAnswer(r: Processing, p: Pending, answer: Answer): AnswerCheck {
  const target = p.activity.target;
  const parsed = r.functions.parse({ kind: "input", definition: target }, p.input);
  if (parsed instanceof Failed) return halt(issueViolation(target, parsed));
  if ("error" in parsed) return { checked: { violation: inputFault(r, target, p.requester, parsed.error) } };
  const input = parsed.value;
  const failedRequires = firstFalse(
    (condition) => r.functions.inputRequirement(target, condition, input),
    requiresOf(r.st.structure, target),
  );
  if (failedRequires instanceof Failed) return halt(issueViolation(target, failedRequires));
  const broken = (failedEnsures?: string) => brokenAssumption(p.id, target, answer, failedRequires, failedEnsures);
  const checked = decodedAnswer(r, p, answer);
  if ("violation" in checked || checked.decoded.result === "rejected" || failedRequires !== undefined)
    return { assumption: broken(), checked };
  const { output } = checked.decoded;
  if (p.activity.keyword === "sends") return { assumption: broken(), checked, accepted: { input, output, events: [] } };
  const failedEnsures = r.functions.resultEnsures(target, input, output, []);
  if (failedEnsures instanceof Failed) return halt(issueViolation(target, failedEnsures));
  return { assumption: broken(failedEnsures), checked };
}

/** Lean's answerRequest. */
function answerRequest(r: Processing, givenId: LineId, p: Pending, answer: Answer): void {
  const s = r.state;
  const { assumption, checked, accepted } = isAssumed(r.st.structure, p.activity.target)
    ? assumedAnswer(r, p, answer)
    : specAnswer(r, p, answer);
  if (assumption !== undefined) report(s, assumption);
  if ("violation" in checked) {
    report(s, checked.violation);
    return;
  }
  const outgoing = s.outgoing.get(idKey(p.id));
  if (outgoing !== undefined && accepted !== undefined) outgoing.accepted = accepted;
  write(s, { dir: "in", type: "answer", id: givenId, to: p.id, answer });
  newMessage(s);
  const step = newStep(s, undefined);
  settled(r, machineOf(p.requester), step, () => deliverAnswer(r, step, p, checked.decoded));
  message(r);
}

/**
 * Lean's answerIn: the answer `a` to the request `to` arrives with the id `id`. A later event's resultOf names the
 * request, so the answer is kept with it, also when the request no longer waits, as after a restart; such an answer is a
 * message with no effect. As in the EIP Idempotent Receiver, an answer that arrives again is not processed again.
 */
export function answerIn(r: Processing, id: LineId, to: LineId, a: Answer): void {
  const s = r.state;
  if (!s.deliveries.has(idKey(id))) {
    s.deliveries.add(idKey(id));
    const outgoing = s.outgoing.get(idKey(to));
    if (outgoing !== undefined) outgoing.answer = a;
    const p = s.pending.find((q) => sameLineId(q.id, to));
    if (p !== undefined) {
      answerRequest(r, id, p, a);
      return;
    }
  }
  write(s, { dir: "in", type: "answer", id, to, answer: a });
  newMessage(s);
  message(r);
}

function startInstance(r: Processing, c: Chart): void {
  const s = r.state;
  const instance = newInstance(c, topId(c.name), { input: {}, context: initialContextOf(r, c.name, {}) }, undefined);
  s.machines.set(instance.id, instance);
  if (c.screen) s.stack.push(instance.id);
}

/** Returns the charts that start when the service begins; a screen that another screen opens does not. */
const starting = (st: Service): Chart[] => [...st.charts.values()].filter((c) => !c.opened);

function startInstances(r: Processing): void {
  for (const c of starting(r.st)) startInstance(r, c);
}

function startRecords(r: Processing): void {
  const { singles } = r.state.records;
  for (const name of r.st.singles) if (!singles.has(name)) singles.set(name, r.functions.singleRecord(name));
}

export function begin(r: Processing): void {
  const s = r.state;
  if (s.started) return;
  s.started = true;
  newMessage(s);
  startRecords(r);
  startInstances(r);
  r.queue.tasks.push(...starting(r.st).map((c): Work => ({ kind: "start", machine: topId(c.name), cause: undefined })));
  message(r);
}

/** Lean's operate: an operation on the screen instance `resource`. */
export function operate(r: Processing, resource: InstanceId, key: string, payload: unknown): void {
  const screen = chartOf(resource);
  const { decoded, found } = writeOperation(r, resource, screen, key, payload);
  const data = { screen: ref(r.st, screen), control: key };
  const top =
    "top" in found
      ? found.top
      : "child" in found
        ? report(r.state, {
            kind: "InvalidInput.coveredByModal",
            definition: null,
            data: { ...data, child: found.child },
          })
        : "payload" in found
          ? report(r.state, {
              kind: "InvalidInput.unofferedPayload",
              definition: null,
              data: { ...data, payload: found.payload },
            })
          : report(r.state, { kind: "InvalidInput.unopenedScreen", definition: null, data });
  const s = r.state;
  newMessage(s);
  const step = newStep(s, undefined);
  settled(r, top.id, step, () => dispatch(r, top.id, key, decoded, step));
  message(r);
}

/**
 * Writes the operation line and reads its payload; returns undefined for a name that is not a control of the screen.
 */
function writeOperation(r: Processing, resource: InstanceId, screen: string, key: string, payload: unknown) {
  const chart = r.st.charts.get(screen);
  const definition = ref(r.st, screen);
  if (chart === undefined) return unownedTarget(r, definition);
  const control = chart.controls.find((c) => c.name === key);
  if (control === undefined)
    return report(r.state, {
      kind: "InvalidInput.unknownControl",
      definition: null,
      data: { screen: definition, control: key },
    });
  const nth = nthOpen(r.state, resource);
  write(r.state, {
    dir: "in",
    type: "operation",
    screen: definition,
    control: key,
    ...(nth === undefined ? {} : { nth }),
    ...(control.hasPayload ? { payload } : {}),
  });
  const parsed = r.functions.parse({ kind: "control", screen: definition, control: key }, payload);
  if (parsed instanceof Failed) return halt(issueViolation(definition, parsed));
  if ("error" in parsed)
    return report(
      r.state,
      withExtra(
        { kind: "InvalidInput.controlPayloadSchema", definition: null, data: { screen: definition, control: key } },
        { error: parsed.error },
      ),
    );
  return { decoded: parsed.value, found: accepting(r, resource, key, parsed) };
}
