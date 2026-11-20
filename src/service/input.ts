import type { DefinitionRef } from "../data/definitionRef.ts";
import { expectFound } from "../data/internalError.ts";
import type { InvalidInput } from "../data/invalidInput.generated.ts";
import type { Answer, LineId } from "../data/trace.generated.ts";
import { lineIdText } from "../data/trace.ts";
import type { Fields, Json } from "../data/values.ts";
import { withExtra } from "../data/violation.ts";
import {
  assumptionMismatch,
  assumptionViolation,
  conditionsOf,
  hasOutput,
  isAssumed,
  rejectionKinds,
  rejectionReasons,
  resultOfMismatch,
} from "../spec/structure.ts";
import { ref, type Service } from "./basic.ts";
import { settled } from "./chart/always.ts";
import type { Chart } from "./chart/basic.ts";
import { deliverAnswer, dispatch } from "./chart/macrostep.ts";
import { commandWork, type Processing, reactions, type Work } from "./chart/queue.ts";
import { initialContextOf, newInstance } from "./chart/request.ts";
import { processCommand } from "./command.ts";
import { Failed, firstFalse, issueViolation, passes } from "./functions.ts";
import { answerAgain, keep, type Request } from "./idempotency.ts";
import { chartOf, type InstanceId, topId } from "./instance.ts";
import { type Emitted, idKey, type Line, sameLineId } from "./message.ts";
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
  type Pending,
  type Run,
  rejectedInput,
  report,
  type State,
  sender,
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
  const step = newStep(s, { kind: "root" });
  const known = s.commandAnswers.get(idKey(id));
  if (known === undefined) {
    const { answer, groups } = processCommand(r, name, input, id, step);
    r.queue.tasks.push(...commandWork(r.st, s, groups, step));
    keep(s.commandAnswers, id, request, answer);
  } else write(s, { dir: "out", type: "answer", to: id, answer: answerAgain(known, request), request: target });
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
  write(s, { dir: "out", type: "answer", to: id, answer: resolveChecked(r, target.name, input), request: target });
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

/** Lean's redeliver. */
function redeliver(r: Processing, event: DefinitionRef, payload: unknown, id: LineId, resultOf?: LineId): void {
  const s = r.state;
  write(s, { dir: "in", type: "event", id, event, payload, ...(resultOf === undefined ? {} : { resultOf }) });
  newMessage(s);
  message(r);
}

/**
 * Lean's receive. The resultOf is only written: the end of the run checks it against the request (checkExchanges),
 * since the event may arrive before or after the answer.
 */
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
  write(s, { dir: "in", type: "event", id, event, payload, ...(resultOf === undefined ? {} : { resultOf }) });
  s.deliveries.add(idKey(id));
  const e: Emitted = { event, payload: parsed.value, encoded: parsed.encoded as Json };
  newMessage(s);
  const step = newStep(s, { kind: "root" });
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

/** The answer to deliver, decoded, or why it is malformed or the sender's fault. */
type Decoded = { readonly decoded: Answer } | { readonly violation: Finding };

/** Lean's decodedAnswer: the answer decoded, or why its rejection kind or output does not match the target. */
function decodedAnswer(r: Run, id: LineId, target: DefinitionRef, answer: Answer): Decoded {
  const request = { requestId: lineIdText(id), target };
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

/**
 * Lean's checkAnswer: the answer to the request `p` decoded for its requester. A spec service parsed the input itself,
 * so its rejection as invalid is the requester's fault. What an assumed peer's answer assumes is checked at the end of
 * the run (checkExchanges).
 */
function checkAnswer(r: Processing, p: Pending, answer: Answer): Decoded {
  const target = p.activity.target;
  const fault = isAssumed(r.st.structure, target)
    ? undefined
    : rejectedInput(r, target, sender(p.requester), p.input, answer);
  return fault === undefined ? decodedAnswer(r, p.id, target, answer) : { violation: fault };
}

/** Lean's answerRequest. */
function answerRequest(r: Processing, givenId: LineId, p: Pending, answer: Answer): void {
  const s = r.state;
  const checked = checkAnswer(r, p, answer);
  if ("violation" in checked) {
    report(s, checked.violation);
    return;
  }
  write(s, { dir: "in", type: "answer", id: givenId, to: p.id, answer });
  newMessage(s);
  const step = newStep(s, { kind: "root" });
  settled(r, machineOf(p.requester), step, () => deliverAnswer(r, step, p, checked.decoded));
  message(r);
}

/**
 * Lean's answerIn: the answer `a` to the request `to` arrives with the id `id`. An answer to a request that no longer
 * waits, as after a restart, is a message with no effect; its line keeps it for the end of the run (checkExchanges). As
 * in the EIP Idempotent Receiver, an answer that arrives again is not processed again.
 */
export function answerIn(r: Processing, id: LineId, to: LineId, a: Answer): void {
  const s = r.state;
  if (!s.deliveries.has(idKey(id))) {
    s.deliveries.add(idKey(id));
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

/**
 * Lean's Exchange: a request that the service sent, as its lines record it: its input as sent, and the answers and the
 * events naming it as their resultOf that arrived, in arrival order. A message that arrived again counts once.
 */
interface Exchange {
  readonly id: LineId;
  readonly target: DefinitionRef;
  readonly sender: string;
  readonly input: unknown;
  readonly answers: readonly Answer[];
  readonly events: readonly { readonly event: DefinitionRef; readonly payload: unknown }[];
}

/** Lean's State.exchanges: the requests that the service sent, in sending order, each with what arrived of it. */
export function exchanges(s: State): Exchange[] {
  const arrived = new Map<string, Line>();
  for (const l of s.lines) if (l.dir === "in" && !arrived.has(idKey(l.id))) arrived.set(idKey(l.id), l);
  const answers = new Map<string, Answer[]>();
  const events = new Map<string, Exchange["events"][number][]>();
  const add = <T>(map: Map<string, T[]>, to: LineId, x: T) => map.set(idKey(to), [...(map.get(idKey(to)) ?? []), x]);
  for (const l of arrived.values()) {
    if (l.type === "answer") add(answers, l.to, l.answer);
    else if (l.type === "event" && l.resultOf !== undefined)
      add(events, l.resultOf, { event: l.event, payload: l.payload });
  }
  return s.lines.flatMap((l) =>
    l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe")
      ? [
          {
            id: l.id,
            target: l.target,
            sender: l.sender,
            input: l.input,
            answers: answers.get(idKey(l.id)) ?? [],
            events: events.get(idKey(l.id)) ?? [],
          },
        ]
      : [],
  );
}

/** Lean's resultOfFinding: the finding of a result event of `x` that cannot be the result of its request. */
function resultOfFinding(r: Run, x: Exchange): InvalidInput | undefined {
  for (const { event } of x.events) {
    const mismatch = resultOfMismatch(r.st.structure, x.target, x.answers, event);
    if (mismatch !== undefined)
      return {
        kind: `InvalidInput.${mismatch}`,
        definition: null,
        data: { event, requestId: lineIdText(x.id), target: x.target },
      };
  }
  return undefined;
}

/**
 * Lean's checkAssumedAnswer: the answer `a` of the request `x` to an assumed peer, whose input decoded as `input`: its
 * rejection kind or output, the target's requires over the input alone, and its ensures, a command's with all the
 * result events.
 */
function checkAssumedAnswer(r: Run, x: Exchange, input: Fields, events: readonly Emitted[], a: Answer): void {
  const { target } = x;
  const checked = decodedAnswer(r, x.id, target, a);
  if ("violation" in checked) {
    report(r.state, checked.violation);
    return;
  }
  const { decoded } = checked;
  const conditions = expectFound(`conditions of ${target.name}`, conditionsOf(r.st.structure, target));
  const failedRequires = firstFalse(
    (condition) => r.functions.inputRequirement(target, condition, input),
    conditions.requires,
  );
  if (failedRequires instanceof Failed) halt(issueViolation(target, failedRequires));
  const failedEnsures =
    decoded.result === "rejected" || failedRequires !== undefined
      ? undefined
      : firstFalse((condition) => {
          const ensured = r.functions.resultEnsures(target, condition, input, decoded.output, events);
          return ensured instanceof Failed ? ensured : passes(ensured);
        }, conditions.ensures);
  if (failedEnsures instanceof Failed) halt(issueViolation(target, failedEnsures));
  const broken = brokenAssumption(x.id, target, a, failedRequires, failedEnsures);
  if (broken !== undefined) report(r.state, broken);
}

/**
 * Lean's checkExchange: the result events of the request `x` against its target, a spec peer's rejection of its input as
 * invalid, and, for an assumed peer, its input against the target's input schema, also when no answer arrived, and each
 * answer. Each answer counts, also one that arrived when the request no longer waited.
 */
function checkExchange(r: Run, x: Exchange): void {
  const { target } = x;
  if (!isAssumed(r.st.structure, target)) {
    for (const a of x.answers) {
      const fault = rejectedInput(r, target, x.sender, x.input, a);
      if (fault !== undefined) report(r.state, fault);
    }
    const found = resultOfFinding(r, x);
    if (found !== undefined) report(r.state, found);
    return;
  }
  const parsed = r.functions.parse({ kind: "input", definition: target }, x.input);
  if (parsed instanceof Failed) halt(issueViolation(target, parsed));
  if ("error" in parsed) halt(inputFault(r, target, x.sender, parsed.error));
  const found = resultOfFinding(r, x);
  if (found !== undefined) report(r.state, found);
  const events = x.events.flatMap(({ event, payload }): Emitted[] => {
    const e = r.functions.parse({ kind: "payload", event }, payload);
    if (e instanceof Failed) return halt(issueViolation(target, e));
    return "error" in e ? [] : [{ event, payload: e.value, encoded: e.encoded as Json }];
  });
  for (const a of x.answers) checkAssumedAnswer(r, x, parsed.value, events, a);
}

/**
 * Lean's checkExchanges: at the end of the run, each request that the service sent is checked once against what its
 * lines record of it, as a Pact provider verification replays the recorded interactions.
 */
export function checkExchanges(r: Run): void {
  for (const x of exchanges(r.state)) checkExchange(r, x);
}

function startInstance(r: Processing, c: Chart): void {
  const s = r.state;
  const instance = newInstance(c, topId(c.name), { input: {}, context: initialContextOf(r, c.name, {}) });
  s.machines.set(instance.id, instance);
  if (c.screen) s.stack.push(instance.id);
}

/** Returns the charts that start when the service begins; a screen that another screen opens does not. */
const starting = (st: Service): Chart[] => [...st.charts.values()].filter((c) => !c.opened);

function startInstances(r: Processing): void {
  for (const c of starting(r.st)) startInstance(r, c);
}

/**
 * Lean's startRecords: writes the record of each single entity that Given left out, as the defaults of its fields, which
 * load checks (Malformed.defaultSchema).
 */
function startRecords(r: Processing): void {
  const { singles } = r.state.records;
  for (const name of r.st.singles) {
    if (singles.has(name)) continue;
    const record = r.functions.defaults({ kind: "record", entity: ref(r.st, name) });
    singles.set(
      name,
      expectFound(`defaults of the single entity ${name}`, record instanceof Failed ? undefined : record),
    );
  }
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
  const step = newStep(s, { kind: "root" });
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
