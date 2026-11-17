import type { DefinitionRef } from "../data/definitionRef.ts";
import type { InvalidInput } from "../data/invalidInput.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import { type ViolationError, withExtra } from "../data/violation.ts";
import {
  type AssumptionMismatch,
  assumptionMismatch,
  hasOutput,
  isAssumed,
  rejectionKinds,
  rejectionReasons,
  requiresOf,
  resultOfMismatch,
} from "../spec/structure.ts";
import { ref, refOf, type Service } from "./basic.ts";
import { settled } from "./chart/always.ts";
import { type Activity, activityRef, type Chart } from "./chart/basic.ts";
import { deliverAnswer, dispatch } from "./chart/macrostep.ts";
import { commandWork, type Processing, reactions, type Work } from "./chart/queue.ts";
import { initialContextOf, newInstance } from "./chart/request.ts";
import { processCommand } from "./command.ts";
import { firstFalse } from "./contract.ts";
import { Failed, issueViolation } from "./functions.ts";
import { answerAgain, keep, type Request } from "./idempotency.ts";
import type { Emit } from "./message.ts";
import { resolveChecked } from "./query.ts";
import { message } from "./queue.ts";
import { accepting } from "./screen/operable.ts";
import { type Accepted, halt, lineId, machineOf, newMessage, newStep, type Pending, report, write } from "./state.ts";

export function send(r: Processing, name: string, input: unknown, given: { readonly id?: string }): void {
  const s = r.state;
  if (!r.st.commands.includes(name)) unownedTarget(r, name);
  const definition = ref(r.st, name);
  const canonicalInput = r.functions.canonical({ kind: "input", definition }, input);
  if (canonicalInput instanceof Failed) halt(issueViolation(definition, canonicalInput));
  const request: Request = { name, input: canonicalInput };
  const id = write(s, { dir: "in", type: "command", ...given, ...request });
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
  const id = write(s, { dir: "in", type: "query", ...given, name, input: canonicalInput });
  newMessage(s);
  write(s, { dir: "out", type: "answer", to: id, answer: resolveChecked(r, name, input) });
  message(r);
}

export function subscribe(r: Processing, name: string, input: unknown, given: { readonly id?: string }): void {
  const s = r.state;
  if (!r.st.queries.includes(name)) unownedTarget(r, name);
  const definition = ref(r.st, name);
  const canonicalInput = r.functions.canonical({ kind: "input", definition }, input);
  if (canonicalInput instanceof Failed) halt(issueViolation(definition, canonicalInput));
  const id = write(s, { dir: "in", type: "subscribe", ...given, name, input: canonicalInput });
  if (!s.subscriptions.subscribe(id, { query: name, input }))
    report(r.state, { kind: "InvalidInput.reusedSubscriptionId", definition: null, data: { subscriptionId: id } });
  newMessage(s);
  message(r);
}

/** Lean's endSubscription: the unsubscribe input that ends the subscription `id`. */
export function endSubscription(r: Processing, id: string): void {
  const s = r.state;
  write(s, { dir: "in", type: "unsubscribe", to: id });
  if (!s.subscriptions.unsubscribe(id))
    report(r.state, { kind: "InvalidInput.unopenedSubscription", definition: null, data: { subscriptionId: id } });
  newMessage(s);
  message(r);
}

/** Lean's resultRequest: the request `handle` whose answer arrived, which an event names as its resultOf. */
function resultRequest(r: Processing, name: string, handle: string): string | undefined {
  const answered = r.state.takenAnswers.get(handle);
  if (answered === undefined)
    return report(r.state, {
      kind: "InvalidInput.resultOfUnansweredRequest",
      definition: null,
      data: { event: refOf(r.st, name), requestId: handle },
    });
  const { target, answer } = answered;
  const event = refOf(r.st, name);
  const mismatch = resultOfMismatch(r.st.structure, target, answer.result === "accepted", event);
  if (mismatch === undefined) return handle;
  return report(r.state, {
    kind: `InvalidInput.${mismatch}`,
    definition: null,
    data: { event, requestId: handle, target },
  });
}

/**
 * Adds the arrived result event `e` to the request `requestId`, an accepted request to an external service's command,
 * and checks the assumed ensures of its result.
 */
function addResult(r: Processing, requestId: string, e: Emit): void {
  const accepted = r.state.results.get(requestId);
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

/** Lean's redeliver. */
function redeliver(
  r: Processing,
  name: string,
  payload: unknown,
  given: { readonly id?: string },
  resultOf?: string,
): void {
  const s = r.state;
  const event = refOf(r.st, name);
  const written = r.functions.canonical({ kind: "payload", event }, payload);
  if (written instanceof Failed) halt(issueViolation(event, written));
  const request = resultOf === undefined ? undefined : resultRequest(r, name, resultOf);
  write(s, {
    dir: "in",
    type: "event",
    ...given,
    name,
    payload: written,
    ...(request === undefined ? {} : { resultOf: request }),
  });
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
  if (s.deliveries.has(lineId(s, given.id, name))) {
    redeliver(r, name, payload, given, resultOf);
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
  const id = write(s, {
    dir: "in",
    type: "event",
    ...given,
    name,
    payload: encoded,
    ...(request === undefined ? {} : { resultOf: request }),
  });
  s.deliveries.add(id);
  const e: Emit = { event: name, payload: decoded };
  if (request !== undefined) addResult(r, request, e);
  newMessage(s);
  const step = newStep(s, undefined);
  r.queue.tasks.push(...reactions(r.st, s, [e], false, step));
  message(r);
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

/** Returns the assumption that an answer to the request `requestId` to `target` breaks (assumptionMismatch). */
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
  readonly written: Written | { readonly malformed: Malformed; readonly error?: ViolationError };
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
): Written | { readonly error: ViolationError } | Failed {
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
 * Checks an answer to the request `p`. When the target is assumed, it also checks the answer against the target's
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

/** Lean's answerRequest. */
export function answerRequest(r: Processing, givenId: string, p: Pending, answer: Answer): Pending | undefined {
  const s = r.state;
  const checked = checkAnswer(r, p, answer);
  if (checked.assumption !== undefined) report(s, checked.assumption);
  if ("malformed" in checked.written) {
    const { malformed, error } = checked.written;
    return report(s, withExtra(malformed, { error }));
  }
  const { written, decoded } = checked.written;
  if (checked.recorded !== undefined) s.results.set(checked.recorded.id, checked.recorded);
  write(s, { dir: "in", type: "answer", id: givenId, to: p.id, answer: written });
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

export function operate(r: Processing, screen: string, key: string, payload: unknown): void {
  const { decoded, found } = writeOperation(r, screen, key, payload);
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

/**
 * Writes the operation line and reads its payload; returns undefined for a name that is not a control of the screen.
 */
function writeOperation(r: Processing, screen: string, key: string, payload: unknown) {
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
  write(r.state, { dir: "in", type: "operation", name, ...(control.hasPayload ? { payload } : {}) });
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
