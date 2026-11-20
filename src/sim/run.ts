import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { expectFound } from "../data/internalError.ts";
import type { InvalidScenario } from "../data/invalidScenario.generated.ts";
import type { Expectation, Fact, Line, Scenario, Template } from "../data/scenario.generated.ts";
import type { Answer, LineId } from "../data/trace.generated.ts";
import { lineIdText } from "../data/trace.ts";
import { byCodePoint, canonicalJson, sameJson } from "../data/values.ts";
import { ref, type Schema } from "../service/basic.ts";
import type { Processing } from "../service/chart/queue.ts";
import { Failed, parseOutside } from "../service/functions.ts";
import { begin, call, checkExchanges, endSubscription, operate, send, subscribe } from "../service/input.ts";
import { chartOf } from "../service/instance.ts";
import { type LineBody, sameLineId } from "../service/message.ts";
import { publish } from "../service/query.ts";
import { fireDue } from "../service/queue.ts";
import { restart } from "../service/restart.ts";
import { accepting } from "../service/screen/operable.ts";
import { Halt, write } from "../service/state.ts";
import type { Structure } from "../spec/structure.generated.ts";
import { contractsListing } from "../spec/structure.ts";
import { given, writtenKey } from "./given.ts";
import {
  act,
  deliver,
  describe,
  type Message,
  noteTo,
  type Opened,
  precedes,
  reportTo,
  running,
  stateOf,
  stopped,
  type World,
} from "./network.ts";
import { receivedId } from "./receive.ts";
import {
  answersOf,
  comparedOr,
  fill,
  json,
  markCreated,
  maskCreated,
  messagesOf,
  Reported,
  screenOf,
  sentBy,
  spanLines,
  targetOf,
} from "./resolve.ts";

type RequestType = Extract<Line, { readonly type: "request" }>["kind"];

const inputSchema = (definition: DefinitionRef): Schema => ({ kind: "input", definition });
const payloadSchema = (event: DefinitionRef): Schema => ({ kind: "payload", event });

/** Lean's comparedAnswer: as it is when no request names a target. */
function comparedAnswer(r: Processing, target: DefinitionRef | undefined, a: Answer): unknown {
  if (target === undefined) return a;
  const schema: Schema = { kind: "output", definition: target };
  if (a.result === "accepted" && a.output !== undefined)
    return { result: "accepted", output: comparedOr(r, schema, a.output) };
  if (a.result === "fulfilled") return { result: "fulfilled", output: comparedOr(r, schema, a.output) };
  return a;
}

/** Lean's comparedAnswerValue. */
function comparedAnswerValue(r: Processing, target: DefinitionRef | undefined, v: unknown): unknown {
  const a = answerOfValue(v);
  return a === undefined ? v : comparedAnswer(r, target, a);
}

function reportedHere(violation: Parameters<typeof reportTo>[1]): never {
  throw new Reported(violation);
}

const processingOf = (w: World, service: string): Processing | undefined => w.services.get(service)?.processing;

const hasCreated = (t: Template): boolean => t.holes.some((h) => h.fill.type === "created");

/** Lean's Fact.picks. */
function factPicks(f: Fact): Template[] {
  switch (f.type) {
    case "request":
      return f.input === undefined ? [] : [f.input, ...templatePicks(f.input)];
    case "event":
      return f.payload === undefined ? [] : [f.payload, ...templatePicks(f.payload)];
    case "end":
      return factPicks(f.subscription);
    default:
      return [];
  }
}

/** Lean's Template.picks. */
const templatePicks = (t: Template): Template[] =>
  t.holes.flatMap((h) => (h.fill.type === "ref" ? factPicks(h.fill.value.fact) : []));

/** Lean's Line.written. */
function lineWritten(l: Line): Template[] {
  switch (l.type) {
    case "request":
      return [l.input];
    case "operate":
      return [l.payload];
    case "answer":
      return [l.answer];
    case "emit":
      return [l.payload];
    default:
      return [];
  }
}

/** Lean's Line.facts. */
function lineFacts(l: Line): Fact[] {
  switch (l.type) {
    case "operate":
    case "look":
      return [l.screen];
    case "answer":
    case "leaveUnanswered":
      return [l.request];
    case "deliver":
    case "redeliver":
    case "lose":
    case "refuse":
    case "leaveInFlight":
      return [l.message];
    case "emit":
      return l.resultOf === undefined ? [] : [l.resultOf];
    default:
      return [];
  }
}

/** Lean's Line.picks. */
const linePicks = (l: Line): Template[] => [
  ...lineFacts(l).flatMap(factPicks),
  ...lineWritten(l).flatMap(templatePicks),
];

/** Lean's Expectation.line. */
const expectationLine = (e: Expectation): number => (e.type === "offered" ? e.look : e.line);

/** Lean's Expectation.written. */
function expectationWritten(e: Expectation): Template[] {
  switch (e.type) {
    case "answered":
      return [...e.answers];
    case "emitted":
      return e.events.map((ev) => ev.payload);
    case "requested":
      return e.requests.map((q) => q.input);
    case "offered":
      return e.payload === undefined ? [] : [e.payload];
  }
}

/** Lean's Expectation.picks. */
const expectationPicks = (e: Expectation): Template[] => [
  ...(e.type === "requested" ? e.ends.flatMap(factPicks) : []),
  ...expectationWritten(e).flatMap(templatePicks),
];

/** Lean's World.checkWritten. */
function checkWritten(
  w: World,
  line: number,
  written: readonly Template[],
  picks: readonly Template[],
  allowed: boolean,
): InvalidScenario | undefined {
  if (picks.some(hasCreated) || (!allowed && written.some(hasCreated)))
    return { kind: "InvalidScenario.misplacedCreated", definition: null, data: { scenarioLine: line } };
  for (const t of [...written, ...picks]) {
    const found = writtenKey(w, t.value);
    if (found !== undefined)
      return {
        kind: "InvalidScenario.writtenKey",
        definition: null,
        data: { scenarioLine: line, key: found[0], entity: found[1] },
      };
  }
  return undefined;
}

/** Lean's World.recordSent: the first `in` line from `before` on, or the one with id `id`. */
function recordSent(w: World, i: number, service: string, before: number, id?: LineId): void {
  const lines = stateOf(w, service)?.lines ?? [];
  const position = lines.findIndex(
    (line, n) => n >= before && line.dir === "in" && (id === undefined || sameLineId(line.id, id)),
  );
  const l = lines[position];
  if (l === undefined || w.sent.some((s) => s.line === i && s.receiver === service && sameLineId(s.id, l.id))) return;
  w.sent.push({ line: i, receiver: service, id: l.id, position });
}

/** Lean's World.forEach: `f` takes each of `xs` until the world stops. */
function forEach<T>(w: World, xs: readonly T[], f: (x: T) => void): void {
  for (const x of xs) {
    if (stopped(w)) return;
    f(x);
  }
}

/** Lean's requestOf. */
function requestOf(
  type: RequestType,
  target: DefinitionRef,
  id: LineId | undefined,
  v: unknown,
): (r: Processing) => void {
  const given = id === undefined ? {} : { id };
  return (r) => {
    if (type === "command") send(r, target, v, given);
    else if (type === "query") call(r, target, v, given);
    else subscribe(r, target, v, given);
  };
}

/** Lean's World.clientRequest. */
function clientRequest(
  w: World,
  i: number,
  type: RequestType,
  target: DefinitionRef,
  input: Template,
  sameIdAs: number | undefined,
): void {
  const receiver = target.service;
  const p = processingOf(w, receiver);
  if (!running(w.roles.get(receiver)) || p === undefined) wrongRole(i, receiver);
  const v = fill(w, i, input);
  let id: LineId | undefined;
  if (sameIdAs !== undefined) {
    const [s] = sentBy(w, sameIdAs);
    if (s === undefined)
      reportedHere({
        kind: "InvalidScenario.unresolvedReference",
        definition: null,
        data: { scenarioLine: i, fact: { type: "line", index: sameIdAs } },
      });
    id = s.id;
  }
  const before = p.state.lines.length;
  act(w, { type: "line", index: i }, receiver, requestOf(type, target, id, v));
  recordSent(w, i, receiver, before);
}

/** Lean's World.carry. */
const carry = (w: World, i: number, k: number): void => {
  w.carried.push([i, k]);
};

/** Lean's World.stated. */
function stated(w: World, i: number, m: Message): void {
  if (!running(w.roles.get(m.receiver))) {
    reportTo(w, {
      kind: "InvalidScenario.wrongRole",
      definition: null,
      data: { scenarioLine: i, service: m.receiver },
    });
    return;
  }
  w.messages.push(m);
  carry(w, i, w.messages.length - 1);
}

/** Lean's World.nextId. */
function nextId(w: World, peer: string, name: string): LineId {
  const byName = w.counts.get(peer) ?? new Map<string, number>();
  w.counts.set(peer, byName);
  const n = (byName.get(name) ?? 0) + 1;
  byName.set(name, n);
  return { kind: "own", id: `${name}#${n}` };
}

/** Lean's bodyOf. */
const bodyOf = (type: RequestType, target: DefinitionRef, input: unknown): LineBody => ({ type, target, input });

/** Lean's World.sameValue. */
function sameValue(
  w: World,
  r: Processing,
  schema: Schema,
  peer: string,
  t: Template,
  expected: unknown,
  actual: unknown,
): boolean {
  const e = markCreated(t, expected);
  return sameJson(comparedOr(r, schema, e), comparedOr(r, schema, maskCreated(w, peer, t, expected, actual)));
}

const isCarried = (w: World, k: number): boolean => w.carried.some(([, j]) => j === k);

/** Lean's World.peerMessage. */
function peerMessage(w: World, i: number, peer: string, fits: (m: Message) => boolean): number {
  const k = w.messages.findIndex((m, k) => m.status === "inFlight" && m.sender === peer && !isCarried(w, k) && fits(m));
  if (k >= 0) return k;
  return reportedHere({ kind: "InvalidScenario.unpairedPeerLine", definition: null, data: { scenarioLine: i, peer } });
}

const isRequest = (l: LineBody): boolean => l.type === "command" || l.type === "query" || l.type === "subscribe";

/** Lean's World.deliverCarried: each running receiver processes the messages `ks` to it in one processing. */
function deliverCarried(w: World, i: number, ks: readonly number[]): void {
  for (const k of ks) carry(w, i, k);
  const receivers = [...new Set(ks.flatMap((k) => w.messages[k]?.receiver ?? []))];
  for (const receiver of receivers) {
    if (stopped(w)) return;
    const mine = ks.filter((k) => w.messages[k]?.receiver === receiver);
    if (!running(w.roles.get(receiver))) {
      for (const k of mine) (w.messages[k] as Message).status = "delivered";
      continue;
    }
    const before = stateOf(w, receiver)?.lines.length ?? 0;
    deliver(w, { type: "line", index: i }, receiver, mine);
    for (const k of mine) {
      const m = w.messages[k] as Message;
      if (!isRequest(m.body)) continue;
      for (const [l, j] of [...w.carried]) if (j === k) recordSent(w, l, receiver, before, receivedId(m.sender, m.id));
    }
  }
}

/** Lean's World.overtaken: reports that line `i`, which delivers `ks`, delivers `k` before an earlier message. */
function checkOvertaken(w: World, i: number, ks: readonly number[], k: number): void {
  const m = w.messages[k];
  if (m === undefined) return;
  const earlier = w.messages
    .slice(0, k)
    .find((n, j) => !ks.includes(j) && n.status === "inFlight" && precedes(w, n, m));
  if (earlier !== undefined)
    reportedHere({
      kind: "InvalidScenario.overtaking",
      definition: null,
      data: { scenarioLine: i, message: describe(m), earlier: describe(earlier) },
    });
}

/** Lean's World.requestIds. */
function requestIds(w: World, i: number, peer: string, fact: Fact): LineId[] {
  const unreceived = (): never =>
    reportedHere({
      kind: "InvalidScenario.unreceivedRequest",
      definition: null,
      data: { scenarioLine: i, peer, fact: json(fact) },
    });
  if (fact.type === "line") {
    const sents = sentBy(w, fact.index);
    if (sents.length === 0)
      return reportedHere({
        kind: "InvalidScenario.unresolvedReference",
        definition: null,
        data: { scenarioLine: i, fact: json(fact) },
      });
    return sents.every((s) => s.receiver === peer) ? sents.map((s) => s.id) : unreceived();
  }
  return messagesOf(w, i, fact).map((k) => {
    const m = w.messages[k] as Message;
    if (m.receiver !== peer || (m.status !== "delivered" && m.status !== "unanswered")) return unreceived();
    return receivedId(m.sender, m.id);
  });
}

/** Lean's offeredAt. */
function offeredAt(r: Processing, o: Opened, control: string, payload: unknown): boolean {
  const parsed = parseOutside(
    r.st,
    r.functions,
    { kind: "control", screen: ref(r.st, chartOf(o.id)), control },
    payload,
  );
  if (parsed instanceof Failed || "error" in parsed) return false;
  try {
    return "top" in accepting(r, o.id, control, parsed);
  } catch (error) {
    if (error instanceof Halt) return false;
    throw error;
  }
}

/** Lean's fireTo. */
function fireTo(time: Temporal.Instant): (r: Processing) => void {
  return (r) => {
    const s = r.state;
    fireDue(r, time);
    if (Temporal.Instant.compare(time, s.now) > 0) {
      s.now = time;
      r.note.wroteNow();
    }
    write(s, { dir: "in", type: "time" });
    publish(r);
  };
}

function wrongRole(i: number, service: string): never {
  return reportedHere({ kind: "InvalidScenario.wrongRole", definition: null, data: { scenarioLine: i, service } });
}

const notInFlight = (i: number, m: Message): never =>
  reportedHere({
    kind: "InvalidScenario.notInFlight",
    definition: null,
    data: { scenarioLine: i, message: describe(m) },
  });

const notDelivered = (i: number, m: Message): never =>
  reportedHere({
    kind: "InvalidScenario.notDelivered",
    definition: null,
    data: { scenarioLine: i, message: describe(m) },
  });

/** Lean's World.answered. */
const answered = (w: World, sender: string, to: LineId): boolean =>
  w.messages.some((n) => n.sender === sender && n.body.type === "answer" && sameLineId(n.body.to, to));

/** Lean's World.take. */
function take(w: World, own: string, lines: readonly Line[], i: number, l: Line) {
  const origin = { type: "line", index: i } as const;
  switch (l.type) {
    case "request": {
      if (l.peer === undefined) return clientRequest(w, i, l.kind, l.target, l.input, l.sameIdAs);
      const peer = l.peer;
      const role = w.roles.get(peer);
      if (role === "external") {
        const v = fill(w, i, l.input);
        const id = nextId(w, peer, l.target.name);
        return stated(w, i, {
          sender: peer,
          receiver: l.target.service,
          id,
          body: bodyOf(l.kind, l.target, v),
          definition: l.target,
          origin,
          status: "inFlight",
        });
      }
      if (role !== "run") return wrongRole(i, peer);
      const v = fill(w, i, l.input);
      const r = processingOf(w, peer) as Processing;
      const k = peerMessage(w, i, peer, (m) => {
        const b = m.body;
        if (b.type !== l.kind || !sameRef(b.target, l.target)) return false;
        return m.receiver === l.target.service && sameValue(w, r, inputSchema(l.target), peer, l.input, v, b.input);
      });
      return carry(w, i, k);
    }
    case "unsubscribe": {
      if (l.peer === undefined) {
        const [s] = sentBy(w, l.subscription);
        if (s === undefined)
          return reportedHere({
            kind: "InvalidScenario.unresolvedReference",
            definition: null,
            data: { scenarioLine: i, fact: { type: "line", index: l.subscription } },
          });
        return act(w, origin, s.receiver, (r) => endSubscription(r, s.id));
      }
      const peer = l.peer;
      return forEach(w, messagesOf(w, i, { type: "line", index: l.subscription }), (j) => {
        const sub = w.messages[j] as Message;
        const role = w.roles.get(peer);
        if (role === "external") {
          const id = nextId(w, peer, "unsubscribe");
          return stated(w, i, {
            sender: peer,
            receiver: sub.receiver,
            id,
            body: { type: "unsubscribe", to: sub.id },
            definition: sub.definition,
            origin,
            status: "inFlight",
          });
        }
        if (role !== "run") return wrongRole(i, peer);
        const k = peerMessage(
          w,
          i,
          peer,
          (m) => m.receiver === sub.receiver && m.body.type === "unsubscribe" && sameLineId(m.body.to, sub.id),
        );
        return carry(w, i, k);
      });
    }
    case "resend": {
      const original = lines[l.line];
      if (original?.type !== "request" || original.peer !== undefined)
        return reportedHere({
          kind: "InvalidScenario.unresolvedReference",
          definition: null,
          data: { scenarioLine: i, fact: { type: "line", index: l.line } },
        });
      return clientRequest(w, i, original.kind, original.target, original.input, l.line);
    }
    case "operate": {
      const o = screenOf(w, i, l.screen);
      if (w.roles.get(o.service) !== "own") return wrongRole(i, o.service);
      const v = fill(w, i, l.payload);
      return act(w, origin, o.service, (r) => operate(r, o.id, l.control, v));
    }
    case "look": {
      const o = screenOf(w, i, l.screen);
      if (processingOf(w, o.service) === undefined) return wrongRole(i, o.service);
      return;
    }
    case "answer": {
      return forEach(w, messagesOf(w, i, l.request), (k) => {
        const m = w.messages[k] as Message;
        if (m.receiver !== l.peer)
          return reportedHere({
            kind: "InvalidScenario.unresolvedReference",
            definition: null,
            data: { scenarioLine: i, fact: json(l.request) },
          });
        const to = receivedId(m.sender, m.id);
        const role = w.roles.get(l.peer);
        if (role === "external") {
          if (m.status !== "delivered") return notDelivered(i, m);
          if (answered(w, l.peer, to) && m.body.type !== "subscribe")
            return reportedHere({
              kind: "InvalidScenario.repeatedAnswer",
              definition: null,
              data: { scenarioLine: i, message: describe(m) },
            });
          const v = fill(w, i, l.answer);
          const a = answerOfValue(v);
          if (a === undefined)
            return reportedHere({
              kind: "InvalidScenario.malformedValue",
              definition: null,
              data: { scenarioLine: i, value: json(v) },
            });
          const id = nextId(w, l.peer, "answer");
          return stated(w, i, {
            sender: l.peer,
            receiver: m.sender,
            id,
            body: { type: "answer", to, answer: a },
            definition: m.definition,
            origin,
            status: "inFlight",
          });
        }
        if (role === "run") {
          const j = w.messages.findIndex(
            (n, k) =>
              n.status === "inFlight" &&
              n.sender === l.peer &&
              n.receiver === m.sender &&
              !isCarried(w, k) &&
              n.body.type === "answer" &&
              sameLineId(n.body.to, to),
          );
          if (j < 0)
            return reportedHere({
              kind: "InvalidScenario.unpairedPeerLine",
              definition: null,
              data: { scenarioLine: i, peer: l.peer },
            });
          const v = fill(w, i, l.answer);
          const reply = w.messages[j] as Message;
          const actual: Answer = reply.body.type === "answer" ? reply.body.answer : { result: "accepted" };
          const r = processingOf(w, l.peer) as Processing;
          const target = targetOf(m);
          const shown = comparedAnswerValue(r, target, maskCreated(w, l.peer, l.answer, v, actual));
          const expected = comparedAnswerValue(r, target, markCreated(l.answer, v));
          if (!sameJson(expected, shown))
            reportTo(w, {
              kind: "InvalidScenario.differentPeerAnswer",
              definition: null,
              data: { scenarioLine: i, expected: json(expected), actual: json(shown) },
            });
          return carry(w, i, j);
        }
        return wrongRole(i, l.peer);
      });
    }
    case "emit": {
      const resultIds = l.resultOf === undefined ? [undefined] : requestIds(w, i, l.peer, l.resultOf);
      const v = fill(w, i, l.payload);
      return forEach(w, resultIds, (resultId) => {
        const role = w.roles.get(l.peer);
        if (role === "external") {
          const id = nextId(w, l.peer, l.event.name);
          const body: LineBody = {
            type: "event",
            event: l.event,
            payload: v,
            ...(resultId === undefined ? {} : { resultOf: resultId }),
          };
          const receivers = [...w.services].filter(([, p]) =>
            p.processing.st.receives.some((e) => sameRef(e, l.event)),
          );
          if (receivers.length === 0)
            return reportedHere({
              kind: "InvalidScenario.unreceivedEvent",
              definition: null,
              data: { scenarioLine: i, event: l.event },
            });
          for (const [r] of receivers)
            stated(w, i, { sender: l.peer, receiver: r, id, body, definition: l.event, origin, status: "inFlight" });
          return;
        }
        if (role === "run") {
          const peer = l.peer;
          const r = processingOf(w, peer) as Processing;
          const k = peerMessage(w, i, peer, (m) => {
            const b = m.body;
            if (b.type !== "event") return false;
            return (
              m.receiver === own &&
              sameRef(b.event, l.event) &&
              sameLineId(b.resultOf, resultId) &&
              sameValue(w, r, payloadSchema(b.event), peer, l.payload, v, b.payload)
            );
          });
          return carry(w, i, k);
        }
        return wrongRole(i, l.peer);
      });
    }
    case "leaveUnanswered": {
      return forEach(w, messagesOf(w, i, l.request), (k) => {
        const m = w.messages[k] as Message;
        if (w.roles.get(l.peer) !== "external" || m.receiver !== l.peer) return wrongRole(i, l.peer);
        if (m.status !== "delivered") return notDelivered(i, m);
        if (answered(w, l.peer, receivedId(m.sender, m.id)) && m.body.type !== "subscribe")
          return reportedHere({
            kind: "InvalidScenario.repeatedAnswer",
            definition: null,
            data: { scenarioLine: i, message: describe(m) },
          });
        m.status = "unanswered";
        return;
      });
    }
    case "deliver": {
      const ks = messagesOf(w, i, l.message);
      for (const k of ks) {
        const m = w.messages[k] as Message;
        if (m.status !== "inFlight") notInFlight(i, m);
        checkOvertaken(w, i, ks, k);
      }
      return deliverCarried(w, i, ks);
    }
    case "redeliver": {
      const ks = messagesOf(w, i, l.message);
      for (const k of ks) {
        const m = w.messages[k] as Message;
        if (m.status !== "delivered") notDelivered(i, m);
        if (!running(w.roles.get(m.receiver))) wrongRole(i, m.receiver);
      }
      return deliverCarried(w, i, ks);
    }
    case "lose": {
      return forEach(w, messagesOf(w, i, l.message), (k) => {
        const m = w.messages[k] as Message;
        if (m.status !== "inFlight") return notInFlight(i, m);
        m.status = "lost";
        return;
      });
    }
    case "refuse": {
      const start = w.messages.length;
      forEach(w, messagesOf(w, i, l.message), (k) => {
        const m = w.messages[k] as Message;
        if (m.status !== "inFlight") return notInFlight(i, m);
        if (!isRequest(m.body))
          return reportedHere({
            kind: "InvalidScenario.unrefusable",
            definition: null,
            data: { scenarioLine: i, message: describe(m) },
          });
        m.status = "lost";
        const to = receivedId(m.sender, m.id);
        const id: LineId = { kind: "own", id: `answer:${lineIdText(m.id)}` };
        const unavailable: Answer = { result: "rejected", rejection: { kind: "unavailable" } };
        w.messages.push({
          sender: m.receiver,
          receiver: m.sender,
          id,
          body: { type: "answer", to, answer: unavailable },
          definition: m.definition,
          origin,
          status: "inFlight",
        });
      });
      return deliverCarried(
        w,
        i,
        w.messages.slice(start).map((_, j) => start + j),
      );
    }
    case "leaveInFlight": {
      return forEach(w, messagesOf(w, i, l.message), (k) => {
        if (w.leftInFlight.some(([, j]) => j === k))
          return reportedHere({
            kind: "InvalidScenario.repeatedInFlight",
            definition: null,
            data: { scenarioLine: i, message: describe(w.messages[k] as Message) },
          });
        w.leftInFlight.push([i, k]);
        return;
      });
    }
    case "at": {
      const time = Temporal.Instant.from(l.time);
      if (Temporal.Instant.compare(time, w.now) <= 0)
        return reportedHere({
          kind: "InvalidScenario.notLater",
          definition: null,
          data: { scenarioLine: i, at: time.toString(), now: w.now.toString() },
        });
      for (const service of w.services.keys()) {
        if (stopped(w)) break;
        act(w, origin, service, fireTo(time));
      }
      w.now = time;
      return;
    }
    case "restart":
      return act(w, origin, own, restart);
  }
}

/** Lean's World.line. */
function line(w: World, own: string, lines: readonly Line[], i: number, l: Line) {
  const allowed =
    (l.type === "request" && l.peer !== undefined && w.roles.get(l.peer) === "run") ||
    ((l.type === "answer" || l.type === "emit") && w.roles.get(l.peer) === "run");
  const r = checkWritten(w, i, lineWritten(l), linePicks(l), allowed);
  if (r !== undefined) return reportTo(w, r);
  return take(w, own, lines, i, l);
}

/** What a look line found for an offered expectation: whether the screen offers it, or the violation of its payload. */
type Found = readonly [number, { readonly offers: boolean } | { readonly violation: InvalidScenario }];

/** Lean's World.found. */
function found(w: World, expectations: readonly Expectation[], i: number, l: Line): Found[] {
  if (l.type !== "look") return [];
  let o: Opened;
  try {
    o = screenOf(w, i, l.screen);
  } catch (error) {
    if (!(error instanceof Reported)) throw error;
    return [];
  }
  const r = processingOf(w, o.service);
  if (r === undefined) return [];
  return expectations.flatMap((e, k): Found[] => {
    if (e.type !== "offered" || e.look !== i) return [];
    try {
      const v = e.payload === undefined ? {} : fill(w, i, e.payload);
      return [[k, { offers: offeredAt(r, o, e.control, v) }]];
    } catch (error) {
      if (!(error instanceof Reported)) throw error;
      return [[k, { violation: error.violation }]];
    }
  });
}

/** Lean's FromValue Answer: the answer that `v` writes, or undefined when it is none. */
function answerOfValue(v: unknown): Answer | undefined {
  if (v === null || typeof v !== "object") return undefined;
  const a = v as Record<string, unknown>;
  switch (a["result"]) {
    case "accepted":
      return a["output"] === undefined ? { result: "accepted" } : { result: "accepted", output: a["output"] };
    case "fulfilled":
      return "output" in a ? { result: "fulfilled", output: a["output"] } : undefined;
    case "rejected": {
      const rejection = a["rejection"] as Record<string, unknown> | undefined;
      const kinds = ["invalid-input", "reused-id", "not-found", "requires", "already-exists", "unavailable"];
      if (rejection === undefined || !kinds.includes(rejection["kind"] as string)) return undefined;
      const reason = rejection["reason"];
      if (reason !== undefined && typeof reason !== "string") return undefined;
      return {
        result: "rejected",
        rejection: { kind: rejection["kind"], ...(reason === undefined ? {} : { reason }) },
      } as Answer;
    }
    default:
      return undefined;
  }
}

/** Lean's World.checkEnd. */
function checkEnd(w: World): void {
  w.messages.forEach((m, k) => {
    if (m.status === "inFlight" && !w.leftInFlight.some(([, j]) => j === k))
      reportTo(w, { kind: "InvalidScenario.leftInFlight", definition: null, data: { message: describe(m) } });
  });
  for (const [i, k] of w.leftInFlight)
    if (w.messages[k]?.status !== "inFlight")
      reportTo(w, { kind: "InvalidScenario.unusedInFlight", definition: null, data: { scenarioLine: i } });
  for (const m of w.messages)
    if (
      m.status === "delivered" &&
      w.roles.get(m.receiver) === "external" &&
      isRequest(m.body) &&
      !answered(w, m.receiver, receivedId(m.sender, m.id))
    )
      reportTo(w, { kind: "InvalidScenario.awaitingAnswer", definition: null, data: { message: describe(m) } });
}

/** Lean's bag. */
const bag = (vs: readonly unknown[]): unknown[] =>
  vs.toSorted((a, b) => byCodePoint(canonicalJson(a), canonicalJson(b)));

/** Lean's World.compared. */
function compared(
  w: World,
  own: string,
  lines: readonly Line[],
  looked: readonly Found[],
  k: number,
  e: Expectation,
): readonly [unknown, unknown] | undefined {
  const r = processingOf(w, own);
  if (r === undefined) return undefined;
  const st = r.st;
  switch (e.type) {
    case "answered": {
      const pairs = sentBy(w, e.line).map((s): readonly [unknown, unknown] => {
        const request = stateOf(w, s.receiver)?.lines[s.position];
        const target =
          request?.type === "command" || request?.type === "query" || request?.type === "subscribe"
            ? request.target
            : undefined;
        const rr = processingOf(w, s.receiver) as Processing;
        const actual = answersOf(w, s).map((a) => comparedAnswer(rr, target, a));
        const expected = e.answers.map((t) => comparedAnswerValue(rr, target, fill(w, e.line, t)));
        return [expected, actual];
      });
      const pair = pairs.find(([expected, actual]) => !sameJson(expected, actual)) ?? pairs[0];
      if (pair === undefined)
        return reportedHere({
          kind: "InvalidScenario.unresolvedReference",
          definition: null,
          data: { scenarioLine: e.line, fact: { type: "line", index: e.line } },
        });
      return pair;
    }
    case "emitted": {
      const listed = st.structure.definitions.some(
        (d) =>
          d.service === own &&
          d.kind === "event" &&
          contractsListing(st.structure, { service: own, name: d.name }).length > 0,
      );
      if (!listed)
        return reportedHere({ kind: "InvalidScenario.vacuousExpectation", definition: null, data: { expectation: k } });
      const actual = spanLines(w, { type: "line", index: e.line }, own).flatMap((l) =>
        l.dir === "out" && l.type === "event" && contractsListing(st.structure, l.event).length > 0
          ? [{ event: l.event, payload: comparedOr(r, payloadSchema(l.event), l.payload) }]
          : [],
      );
      const filled = e.events.map((ev) => [ev.event, fill(w, e.line, ev.payload)] as const);
      const expected = filled.map(([event, v]) => ({
        event,
        payload: comparedOr(r, payloadSchema(event), v),
      }));
      return [bag(expected), bag(actual)];
    }
    case "requested": {
      const span = spanLines(w, { type: "line", index: e.line }, own);
      const actualEnds = span.flatMap((l) => (l.dir === "out" && l.type === "unsubscribe" ? [lineIdText(l.to)] : []));
      const actual = span.flatMap((l) =>
        l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe")
          ? [{ kind: l.type, target: l.target, input: comparedOr(r, inputSchema(l.target), l.input) }]
          : [],
      );
      const filled = e.requests.map((q) => [q, fill(w, e.line, q.input)] as const);
      const expectedEnds = e.ends.flatMap((f) =>
        messagesOf(w, e.line, f).map((k) => lineIdText(expectFound(`message ${k}`, w.messages[k]).id)),
      );
      const expected = filled.map(([q, v]) => ({
        kind: q.kind,
        target: q.target,
        input: comparedOr(r, inputSchema(q.target), v),
      }));
      return [
        { requests: bag(expected), ends: bag(expectedEnds) },
        { requests: bag(actual), ends: bag(actualEnds) },
      ];
    }
    case "offered": {
      if (lines[e.look]?.type !== "look")
        return reportedHere({
          kind: "InvalidScenario.notALook",
          definition: null,
          data: { expectation: k, scenarioLine: e.look },
        });
      const at = looked.find(([j]) => j === k)?.[1];
      if (at === undefined) return undefined;
      if ("violation" in at) throw new Reported(at.violation);
      return [e.offered, at.offers];
    }
  }
}

/** Lean's World.expect. */
function expect(
  w: World,
  own: string,
  lines: readonly Line[],
  expectations: readonly Expectation[],
  looked: readonly Found[],
): void {
  expectations.forEach((e, k) => {
    const r = checkWritten(w, expectationLine(e), expectationWritten(e), expectationPicks(e), false);
    if (r !== undefined) {
      noteTo(w, r);
      return;
    }
    try {
      const both = compared(w, own, lines, looked, k, e);
      if (both === undefined) return;
      const [expected, actual] = both;
      if (!sameJson(expected, actual))
        noteTo(w, {
          kind: "InvalidScenario.unmetExpectation",
          definition: null,
          data: { expectation: k, expected: json(expected), actual: json(actual) },
        });
    } catch (error) {
      if (!(error instanceof Reported)) throw error;
      noteTo(w, error.violation);
    }
  });
}

/** Lean's World.execute, and with `looked`, World.stepFinding: what each look line found for Then is added to it. */
function executeLines(w: World, sc: Scenario, looked?: Found[]): void {
  for (const service of w.services.keys()) if (!stopped(w)) act(w, { type: "startup" }, service, begin);
  sc.lines.forEach((l, i) => {
    if (stopped(w)) return;
    looked?.push(...found(w, sc.expectations, i, l));
    try {
      line(w, sc.service, sc.lines, i, l);
    } catch (error) {
      if (!(error instanceof Reported)) throw error;
      reportTo(w, error.violation);
    }
  });
}

/** Lean's execute. */
export function execute(structure: Structure, w: World, sc: Scenario): World {
  given(w, structure, sc);
  if (w.violations.length > 0) return w;
  executeLines(w, sc);
  return w;
}

/** Lean's World.ended. */
function ended(w: World): void {
  if (stopped(w)) return;
  for (const p of w.services.values())
    try {
      checkExchanges(p.processing);
    } catch (error) {
      if (!(error instanceof Halt)) throw error;
      p.halted = error.violation;
    }
}

/** Lean's simulate. */
export function simulate(structure: Structure, w: World, sc: Scenario): World {
  given(w, structure, sc);
  if (w.violations.length > 0) return w;
  const looked: Found[] = [];
  executeLines(w, sc, looked);
  ended(w);
  if (stopped(w)) return w;
  checkEnd(w);
  expect(w, sc.service, sc.lines, sc.expectations, looked);
  return w;
}
