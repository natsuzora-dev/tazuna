import type { DefinitionRef } from "../../data/definitionRef.ts";
import type { InvalidInput } from "../../data/invalidInput.generated.ts";
import type { Step } from "../../data/step.generated.ts";
import type { Answer } from "../../data/trace.generated.ts";
import { type Json, overlay, plain, stringsOf } from "../../data/values.ts";
import { type ProblemError, withExtra } from "../../data/violation.ts";
import {
  type AssumptionMismatch,
  assumptionMismatch,
  hasOutput,
  isAssumed,
  isKeyOf,
  rejectionKinds,
  rejectionReasons,
  requiresOf,
  resultOfMismatch,
} from "../../syntax/structure.ts";
import { settled } from "../chart/always.ts";
import { type Activity, activityRef, type Chart } from "../chart/basic.ts";
import { deliverAnswer, dispatch } from "../chart/macrostep.ts";
import { commandWork, type Processing, reactions, type Work } from "../chart/queue.ts";
import { initialContextOf, newInstance } from "../chart/request.ts";
import { Failed, issueViolation } from "../functions.ts";
import type { Emit } from "../message.ts";
import { accepting } from "../screen/operable.ts";
import { ref, refOf, type Service } from "../service/basic.ts";
import { processCommand } from "../service/command.ts";
import { firstFalse } from "../service/contract.ts";
import {
  answerAgain,
  type Delivery,
  keep,
  malformedRedelivery,
  type Request,
  sameDelivery,
} from "../service/idempotency.ts";
import { resolveChecked } from "../service/query.ts";
import {
  type Accepted,
  halt,
  lineId,
  machineOf,
  newMessage,
  newStep,
  type Pending,
  report,
  type State,
  senderOf,
  write,
  writeInput,
} from "../state.ts";
import { fireDue, message } from "./queue.ts";

export function send(r: Processing, name: string, input: unknown, given: { readonly id?: string }): void {
  const s = r.state;
  if (!r.st.commands.includes(name)) unownedTarget(r, name);
  const definition = ref(r.st, name);
  const canonicalInput = r.functions.canonical({ kind: "input", definition }, input);
  if (canonicalInput instanceof Failed) halt(issueViolation(definition, canonicalInput));
  const request: Request = { name, input: canonicalInput };
  const id = writeInput(s, { dir: "in", type: "command", ...given, ...request });
  newMessage(s);
  const step = newStep(s, undefined);
  const known = s.commandAnswers.get(id);
  if (known === undefined) {
    const { answer, emits } = processCommand(r, name, input, id, step);
    r.queue.tasks.push(...commandWork(r.st, s, emits, step));
    keep(s.commandAnswers, id, request, answer);
  } else write(s, { dir: "out", type: "answer", to: id, answer: answerAgain(known, request) });
  message(r);
}

function unownedTarget(r: Processing, name: string): never {
  return report(r.state, { kind: "InvalidInput.unownedTarget", definition: null, data: { target: refOf(r.st, name) } });
}

export function call(r: Processing, name: string, input: unknown, given: { readonly id?: string }): void {
  const s = r.state;
  if (!r.st.queries.includes(name)) unownedTarget(r, name);
  const definition = ref(r.st, name);
  const canonicalInput = r.functions.canonical({ kind: "input", definition }, input);
  if (canonicalInput instanceof Failed) halt(issueViolation(definition, canonicalInput));
  const id = writeInput(s, { dir: "in", type: "query", ...given, name, input: canonicalInput });
  newMessage(s);
  write(s, { dir: "out", type: "answer", to: id, answer: resolveChecked(r, name, input) });
  message(r);
}

export function subscribe(
  r: Processing,
  name: string,
  input: unknown,
  given: { readonly id?: string },
  handle: string | undefined,
): void {
  const s = r.state;
  if (!r.st.queries.includes(name)) unownedTarget(r, name);
  const definition = ref(r.st, name);
  const canonicalInput = r.functions.canonical({ kind: "input", definition }, input);
  if (canonicalInput instanceof Failed) halt(issueViolation(definition, canonicalInput));
  const id = writeInput(s, { dir: "in", type: "subscribe", ...given, name, input: canonicalInput });
  if (handle !== undefined) s.subscribed.set(handle, id);
  if (!s.subscriptions.subscribe(id, { query: name, input }))
    report(r.state, { kind: "InvalidInput.reusedSubscriptionId", definition: null, data: { subscriptionId: id } });
  newMessage(s);
  message(r);
}

/**
 * Lean's endSubscription. A checked scenario names by handle only a subscribe input before it
 * (Illegal.namedInputUnplaced), so the handle names a subscription that the input opened.
 */
export function endSubscription(r: Processing, subscription: Ended): void {
  const id = "to" in subscription ? subscription.to : r.state.subscribed.get(subscription.handle);
  if (id !== undefined) endOpened(r, id);
}

function endOpened(r: Processing, id: string): void {
  const s = r.state;
  writeInput(s, { dir: "in", type: "unsubscribe", to: id });
  if (!s.subscriptions.unsubscribe(id))
    report(r.state, { kind: "InvalidInput.unopenedSubscription", definition: null, data: { subscriptionId: id } });
  newMessage(s);
  message(r);
}

/**
 * Returns the request whose answer the latest mock input with handle `handle` gave. A checked scenario names only a mock input
 * before the event (Illegal.namedInputUnplaced), so that mock has been placed. Returns undefined when that mock reported
 * missingWaitingRequest or missingStaleRequest, and after reporting that the request cannot have the event as its
 * result (resultOfMismatch).
 */
function resultRequest(r: Processing, name: string, handle: string): Pending | undefined {
  const answered = r.state.mocks.get(handle);
  if (answered === undefined) return undefined;
  const { request, answer } = answered;
  const target = activityRef(request.activity);
  const event = refOf(r.st, name);
  const mismatch = resultOfMismatch(r.st.structure, target, answer.result === "accepted", event);
  if (mismatch === undefined) return request;
  return report(r.state, {
    kind: `InvalidInput.${mismatch}`,
    definition: null,
    data: { event, requestId: request.id, target },
  });
}

/**
 * Adds the arrived result event `e` to `request`, an accepted request to an external service's command, and checks the
 * assumed ensures of its result.
 */
function addResult(r: Processing, request: Pending, e: Emit): void {
  const accepted = r.state.results.get(request.id);
  if (accepted === undefined) return;
  accepted.events.push(e);
  const target = activityRef(accepted.activity);
  const failed = r.functions.resultEnsures(accepted.activity.target, accepted.input, accepted.output, accepted.events);
  if (failed instanceof Failed) halt(issueViolation(target, failed));
  if (failed !== undefined)
    report(r.state, {
      kind: "InvalidInput.failedAssumedEnsures",
      definition: null,
      data: { requestId: accepted.id, target, condition: failed },
    });
}

function redeliver(
  r: Processing,
  name: string,
  payload: unknown,
  given: { readonly id?: string },
  first: Delivery,
  resultOf?: string,
): void {
  const s = r.state;
  const event = refOf(r.st, name);
  const written = r.functions.canonical({ kind: "payload", event }, payload);
  if (written instanceof Failed) halt(issueViolation(event, written));
  const request = resultOf === undefined ? undefined : resultRequest(r, name, resultOf);
  const id = writeInput(s, {
    dir: "in",
    type: "event",
    ...given,
    name,
    payload: written,
    ...(request === undefined ? {} : { resultOf: request.id }),
  });
  const delivered: Delivery = { event, payload: plain(written) };
  if (!sameDelivery(first, delivered)) report(r.state, malformedRedelivery(id, first, delivered));
  newMessage(s);
  message(r);
}

export function receive(
  r: Processing,
  name: string,
  payload: unknown,
  given: { readonly id?: string },
  resultOf?: string,
): void {
  const s = r.state;
  if (!r.st.received.includes(name))
    report(r.state, { kind: "InvalidInput.unlistedEvent", definition: null, data: { event: refOf(r.st, name) } });
  const first = s.eventDeliveries.get(lineId(s, given.id, name));
  if (first !== undefined) {
    redeliver(r, name, payload, given, first, resultOf);
    return;
  }
  const event = refOf(r.st, name);
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
  const { value: decoded, encoded } = parsed;
  const request = resultOf === undefined ? undefined : resultRequest(r, name, resultOf);
  const id = writeInput(s, {
    dir: "in",
    type: "event",
    ...given,
    name,
    payload: encoded,
    ...(request === undefined ? {} : { resultOf: request.id }),
  });
  s.eventDeliveries.set(id, { event, payload: plain(encoded) });
  const e: Emit = { event: name, payload: decoded };
  if (request !== undefined) addResult(r, request, e);
  newMessage(s);
  const step = newStep(s, undefined);
  r.queue.tasks.push(...reactions(r.st, s, [e], false, step));
  message(r);
}

type Mock = Extract<Step, { readonly type: "answer" }>;

type Ended = Extract<Step, { readonly type: "unsubscribe" }>["subscription"];

type Choice = NonNullable<Mock["choice"]>;

const choosesStale = (choice: Choice | undefined): boolean =>
  choice !== undefined && !("to" in choice) && choice.stale === true;

/** Lean's State.waiting: the requests from `sender` to `name` that wait, stale exactly when `stale` is, in sending order. */
function waiting(s: State, sender: string, name: string, stale: boolean): Pending[] {
  return s.pending.filter(
    (p) => p.stale === stale && p.activity.target === name && senderOf(s, p.requester) === sender,
  );
}

/**
 * Lean's chosen: the requests of `ps` whose input has each field of the mock input `input` equal, at any depth, an
 * array or any other value as a whole.
 */
function chosen(r: Processing, name: string, input: unknown, ps: readonly Pending[]): Pending[] {
  const definition = refOf(r.st, name);
  return ps.filter((p) => {
    const v = r.functions.canonical({ kind: "input", definition }, overlay(JSON.parse(p.input), input));
    if (v instanceof Failed) return halt(issueViolation(definition, v));
    return JSON.stringify(v) === p.input;
  });
}

/**
 * Lean's State.answering: the request that the mock answers, the longest-waiting of those that its choice allows, or why
 * it answers none.
 */
function answering(r: Processing, sender: string, name: string, choice: Choice | undefined): Pending | InvalidInput {
  const s = r.state;
  const stale = choosesStale(choice);
  const ps =
    choice !== undefined && "to" in choice
      ? s.pending.filter((p) => p.id === choice.to && p.activity.target === name && senderOf(s, p.requester) === sender)
      : choice?.input === undefined
        ? waiting(s, sender, name, stale)
        : chosen(r, name, choice.input, waiting(s, sender, name, stale));
  const refs = { sender: refOf(r.st, sender), target: refOf(r.st, name) };
  const inputs = [...new Set(ps.map((p) => p.input))];
  if (inputs.length > 1)
    return {
      kind: "InvalidInput.ambiguousMock",
      definition: null,
      data: { ...refs, inputs: inputs.map((i) => JSON.parse(i) as Json) },
    };
  const p = ps.toSorted((a, b) => a.turn - b.turn)[0];
  if (p !== undefined) return p;
  return {
    kind: stale ? "InvalidInput.missingStaleRequest" : "InvalidInput.missingWaitingRequest",
    definition: null,
    data: refs,
  };
}

type Assumption = Extract<
  InvalidInput,
  { readonly kind: `InvalidInput.${"rejectedAssumedRequires" | "failedAssumedRequires" | "failedAssumedEnsures"}` }
>;

function assumptionFinding(requestId: string, target: DefinitionRef, m: AssumptionMismatch): Assumption {
  return m.kind === "rejectedAssumedRequires"
    ? { kind: `InvalidInput.${m.kind}`, definition: null, data: { requestId, target } }
    : { kind: `InvalidInput.${m.kind}`, definition: null, data: { requestId, target, condition: m.condition } };
}

/** Returns the assumption that a mock's answer to the request `requestId` to `target` breaks (assumptionMismatch). */
function brokenAssumption(
  requestId: string,
  target: DefinitionRef,
  answer: Answer,
  failedRequires: string | undefined,
  failedEnsures: string | undefined,
): Assumption | undefined {
  const m = assumptionMismatch(answer, failedRequires, failedEnsures);
  return m === undefined ? undefined : assumptionFinding(requestId, target, m);
}

type Malformed = Extract<
  InvalidInput,
  { readonly kind: `InvalidInput.${"unlistedRejectionKind" | "unlistedRejectionReason" | "answerOutputSchema"}` }
>;

interface Written {
  /** The answer to write, with its output canonical. */
  readonly written: Answer;
  /** The answer to deliver, with its output decoded. */
  readonly decoded: Answer;
}

interface AnswerCheck {
  /** The assumption that the answer breaks, reported without halting. */
  readonly assumption: Assumption | undefined;
  /** The answer to write, or the reason that it is malformed. */
  readonly written: Written | { readonly malformed: Malformed; readonly error?: ProblemError };
  /** An external command's acceptance, recorded to check its result events later. */
  readonly recorded?: Accepted;
}

/**
 * Returns the answer as written and decoded, or its error when the output does not match the target's output schema.
 */
function writtenAnswer(
  r: Processing,
  a: Activity,
  answer: Answer,
): Written | { readonly error: ProblemError } | Failed {
  const target = activityRef(a);
  if (!hasOutput(r.st.structure, target) || answer.result === "rejected") return { written: answer, decoded: answer };
  const parsed = r.functions.parse({ kind: "output", definition: target }, answer.output);
  if (parsed instanceof Failed || "error" in parsed) return parsed;
  return {
    written: { ...answer, output: parsed.encoded } as Answer,
    decoded: { ...answer, output: parsed.value } as Answer,
  };
}

/**
 * Checks a mock's answer to the request `p`. When the target is assumed, it also checks the answer against the target's
 * requires over the input alone and its ensures that read no records.
 */
function checkAnswer(r: Processing, p: Pending, answer: Answer): AnswerCheck {
  const definition = activityRef(p.activity);
  const name = p.activity.target;
  const structure = r.st.structure;
  const assumed = isAssumed(structure, definition);
  const requires = assumed ? requiresOf(structure, definition) : [];
  let failedRequires: string | undefined;
  if (requires.length > 0) {
    const failed = firstFalse((condition) => r.functions.inputRequirement(name, condition, p.value), requires);
    if (failed instanceof Failed) return halt(issueViolation(definition, failed));
    failedRequires = failed;
  }
  const broken = (failedEnsures?: string): Assumption | undefined =>
    assumed ? brokenAssumption(p.id, definition, answer, failedRequires, failedEnsures) : undefined;
  if (answer.result === "rejected") {
    const { rejection } = answer;
    const data = { requestId: p.id, target: definition, rejection };
    const listed = rejectionKinds(structure, r.st.service, definition);
    const written: AnswerCheck["written"] = !listed.includes(rejection.kind)
      ? { malformed: { kind: "InvalidInput.unlistedRejectionKind", definition: null, data } }
      : rejection.kind === "requires" && !rejectionReasons(structure, definition).includes(rejection.reason ?? "")
        ? { malformed: { kind: "InvalidInput.unlistedRejectionReason", definition: null, data } }
        : { written: answer, decoded: answer };
    return { assumption: broken(), written };
  }
  const written = writtenAnswer(r, p.activity, answer);
  if (written instanceof Failed) return halt(issueViolation(definition, written));
  if ("error" in written)
    return {
      assumption: broken(),
      written: {
        malformed: {
          kind: "InvalidInput.answerOutputSchema",
          definition: null,
          data: { requestId: p.id, target: definition },
        },
        error: written.error,
      },
    };
  if (!assumed || failedRequires !== undefined) return { assumption: broken(), written };
  const output = written.decoded.result === "rejected" ? undefined : written.decoded.output;
  const failedEnsures = r.functions.resultEnsures(name, p.value, output, []);
  if (failedEnsures instanceof Failed) return halt(issueViolation(definition, failedEnsures));
  return {
    assumption: broken(failedEnsures),
    written,
    ...(p.activity.keyword === "sends"
      ? { recorded: { id: p.id, activity: p.activity, input: p.value, output, events: [] } }
      : {}),
  };
}

export function mock(r: Processing, value: Mock): Pending | undefined {
  const s = r.state;
  const { sender, target: name } = value;
  const p = answering(r, sender, name, value.choice);
  if ("kind" in p) return report(s, p);
  if (value.handle !== undefined) s.mocks.set(value.handle, { request: p, answer: value.answer });
  const checked = checkAnswer(r, p, value.answer);
  if (checked.assumption !== undefined) report(s, checked.assumption);
  if ("malformed" in checked.written) {
    const { malformed, error } = checked.written;
    return report(s, withExtra(malformed, { error }));
  }
  const { written, decoded } = checked.written;
  if (checked.recorded !== undefined) s.results.set(checked.recorded.id, checked.recorded);
  writeInput(s, { dir: "in", type: "answer", to: p.id, answer: written });
  newMessage(s);
  const step = newStep(s, undefined);
  settled(r, machineOf(p.requester), step, () => deliverAnswer(r, step, p, decoded));
  message(r);
  return p;
}

function startInstance(r: Processing, c: Chart): void {
  const s = r.state;
  const instance = newInstance(r.st, c, c.name, { input: {}, context: initialContextOf(r, c.name, {}) }, undefined);
  s.machines.set(instance.resource, instance);
  if (c.screen) s.stack.push(instance.resource);
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
  r.queue.tasks.push(...starting(r.st).map((c): Work => ({ kind: "start", machine: c.name, cause: undefined })));
  message(r);
}

/**
 * Ends the input: reports the entries of its `deadlineOrder` that no tie used, then those of its `stepOrder` left
 * unused.
 */
export function checkOrderUsed(r: Processing): void {
  const s = r.state;
  s.inputDeadlineOrder = [];
  if (s.deadlineOrder.length > 0)
    report(r.state, { kind: "InvalidInput.unusedDeadlineOrder", definition: null, data: { entries: s.deadlineOrder } });
  if (s.stepOrder.length > 0)
    report(r.state, { kind: "InvalidInput.unusedStepOrder", definition: null, data: { entries: s.stepOrder } });
  const unused = [...s.keyNames].find(([, names]) => names.length > 0);
  s.keyNames = new Map();
  if (unused !== undefined)
    report(r.state, {
      kind: "InvalidInput.unusedKeys",
      definition: null,
      data: { entity: unused[0], names: unused[1] },
    });
}

/** Lean's Step.Body.values: the values that the input gives the service, an input, a payload, or an answer's output. */
function valuesOf(input: Step): unknown[] {
  switch (input.type) {
    case "command":
    case "query":
    case "subscribe":
      return [input.input];
    case "event":
    case "operation":
    case "unacceptedOperation":
      return [input.payload];
    case "answer":
      return input.answer.result === "rejected" || input.answer.output === undefined ? [] : [input.answer.output];
    default:
      return [];
  }
}

/**
 * Reports the first string of the input's values that has the form of a createKey value of an own entity that createKey
 * has not given yet (InvalidInput.uncreatedKey).
 */
export function checkUncreatedKeys(r: Processing, input: Step): void {
  const { st, state: s } = r;
  for (const value of valuesOf(input).flatMap(stringsOf)) {
    if (s.created.some(([, key]) => key === value)) continue;
    const entity = st.entities.find((e) => !st.singles.includes(e) && isKeyOf(e, value));
    if (entity !== undefined)
      report(s, {
        kind: "InvalidInput.uncreatedKey",
        definition: null,
        data: { recordKey: value, entity: ref(st, entity) },
      });
  }
}

/**
 * Makes the state in which `input` arrives. Every input first advances the time to its own, firing the deadlines due by
 * then; then every input but a restart, which begins the service itself, begins the service if it has not begun.
 */
export function advance(r: Processing, input: Step): void {
  const s = r.state;
  const to = Temporal.Instant.from(input.time);
  if (Temporal.Instant.compare(to, s.now) < 0)
    report(r.state, {
      kind: "InvalidInput.earlierAt",
      definition: null,
      data: { at: to.toString(), now: s.now.toString() },
    });
  fireDue(r, to);
  if (Temporal.Instant.compare(to, s.now) > 0) {
    s.now = to;
    r.note.wroteNow();
  }
  if (input.type !== "restart") begin(r);
}

export function operate(r: Processing, screen: string, key: string, payload: unknown): void {
  const { decoded, found } = writeOperation(r, "operation", screen, key, payload);
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
  settled(r, top.resource, step, () => dispatch(r, top.resource, key, decoded, step));
  message(r);
}

export function cannotOperate(r: Processing, screen: string, key: string, payload: unknown): void {
  const operation = writeOperation(r, "unacceptedOperation", screen, key, payload);
  if ("top" in operation.found)
    report(r.state, {
      kind: "InvalidInput.unexpectedlyAccepted",
      definition: null,
      data: { screen: ref(r.st, screen), control: key },
    });
  newMessage(r.state);
  message(r);
}

/**
 * Writes the operation line and reads its payload; returns undefined for a name that is not a control of the screen.
 */
function writeOperation(
  r: Processing,
  type: "operation" | "unacceptedOperation",
  screen: string,
  key: string,
  payload: unknown,
) {
  const chart = r.st.charts.get(screen);
  if (chart === undefined) return unownedTarget(r, screen);
  const definition = ref(r.st, screen);
  const control = chart.controls.find((c) => c.name === key);
  if (control === undefined)
    return report(r.state, {
      kind: "InvalidInput.unknownControl",
      definition: null,
      data: { screen: definition, control: key },
    });
  const name = `${screen}.${key}`;
  writeInput(r.state, { dir: "in", type, name, ...(control.hasPayload ? { payload } : {}) });
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
  return { decoded: parsed.value, found: accepting(r, screen, key, parsed) };
}
