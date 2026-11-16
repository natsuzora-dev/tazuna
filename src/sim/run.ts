import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Expectation, Fact, Line, Scenario, Template } from "../data/scenario.generated.ts";
import type { Answer, DeadlineId, TraceLine } from "../data/trace.generated.ts";
import { byCodePoint, canonicalJson, stringsOf } from "../data/values.ts";
import { ref, refOf, type Schema, type Service } from "../service/basic.ts";
import type { Processing } from "../service/chart/queue.ts";
import { Failed } from "../service/functions.ts";
import { begin, call, checkOrderUsed, endSubscription, operate, send, subscribe } from "../service/input.ts";
import { fireDue } from "../service/queue.ts";
import { restart } from "../service/restart.ts";
import { accepting, topOf } from "../service/screen/operable.ts";
import { Halt, writeInput } from "../service/state.ts";
import type { Structure } from "../syntax/structure.generated.ts";
import { contractsListing, isKeyOf, refOfTraceName, traceNameOfRef } from "../syntax/structure.ts";
import { given } from "./given.ts";
import {
  act,
  deliver,
  describe,
  type Message,
  noteTo,
  type Opened,
  reportTo,
  running,
  sameChannel,
  stateOf,
  stopped,
  type World,
} from "./network.ts";
import { receivedId } from "./participant.ts";
import {
  answersOf,
  fill,
  json,
  markCreated,
  maskCreated,
  messageOf,
  Reported,
  screenOf,
  sentBy,
  spanLines,
  targetOf,
} from "./resolve.ts";

type RequestType = Extract<Line, { readonly type: "request" }>["kind"];

/** Lean's comparedOr. */
function comparedOr(r: Processing, schema: Schema, v: unknown): unknown {
  const c = r.functions.unordered(schema, v);
  return c instanceof Failed ? v : c;
}

const inputSchema = (st: Service, name: string): Schema => ({ kind: "input", definition: refOf(st, name) });
const outputSchema = (st: Service, name: string): Schema => ({ kind: "output", definition: refOf(st, name) });
const payloadSchema = (st: Service, name: string): Schema => ({ kind: "payload", event: refOf(st, name) });

/** Lean's comparedAnswer. */
function comparedAnswer(r: Processing, target: string, a: Answer): unknown {
  if (a.result === "accepted" && a.output !== undefined)
    return { result: "accepted", output: comparedOr(r, outputSchema(r.st, target), a.output) };
  if (a.result === "fulfilled")
    return { result: "fulfilled", output: comparedOr(r, outputSchema(r.st, target), a.output) };
  return a;
}

/** Lean's comparedAnswerValue. */
function comparedAnswerValue(r: Processing, target: string, v: unknown): unknown {
  const a = answerOfValue(v);
  return a === undefined ? v : comparedAnswer(r, target, a);
}

function reportedHere(report: Parameters<typeof reportTo>[1]): never {
  throw new Reported(report);
}

const processingOf = (w: World, service: string): Processing | undefined => w.participants.get(service)?.processing;

/** Lean's World.uncreated. */
function uncreated(w: World, st: Service, v: unknown): readonly [string, string] | undefined {
  const created = [...w.participants.values()].flatMap((p) => p.processing.state.created.map(([, key]) => key));
  for (const x of stringsOf(v)) {
    if (created.includes(x)) continue;
    const parts = x.split("/");
    const [owner, key] = parts;
    if (parts.length !== 2 || owner === undefined || key === undefined || !w.participants.has(owner)) continue;
    const entity = st.entities.find((e) => !st.singles.includes(e) && isKeyOf(e, key));
    if (entity !== undefined) return [x, entity];
  }
  return undefined;
}

/** Lean's World.recordSent. */
function recordSent(w: World, i: number, service: string, before: number): void {
  const lines = stateOf(w, service)?.lines ?? [];
  const position = lines.findIndex((line, n) => n >= before && line.dir === "in");
  const l = lines[position];
  if (l !== undefined) w.sent.push({ line: i, receiver: service, id: l.id, position });
}

/** Lean's requestOf. */
function requestOf(type: RequestType, name: string, id: string | undefined, v: unknown): (r: Processing) => void {
  const given = id === undefined ? {} : { id };
  return (r) => {
    if (type === "command") send(r, name, v, given);
    else if (type === "query") call(r, name, v, given);
    else subscribe(r, name, v, given, undefined);
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
  if (!running(w.roles.get(receiver)) || p === undefined)
    reportedHere({ kind: "Report.wrongRole", definition: null, data: { scenarioLine: i, service: receiver } });
  const v = fill(w, i, input);
  const found = uncreated(w, p.st, input.value);
  if (found !== undefined)
    reportedHere({
      kind: "Report.uncreatedKey",
      definition: null,
      data: { scenarioLine: i, key: found[0], entity: ref(p.st, found[1]) },
    });
  let id: string | undefined;
  if (sameIdAs !== undefined) {
    const s = sentBy(w, sameIdAs);
    if (s === undefined)
      reportedHere({
        kind: "Report.unresolvedReference",
        definition: null,
        data: { scenarioLine: i, fact: { type: "line", index: sameIdAs } },
      });
    id = s.id;
  }
  const before = p.state.lines.length;
  act(w, { type: "line", index: i }, receiver, requestOf(type, target.name, id, v));
  recordSent(w, i, receiver, before);
}

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
  return (
    canonicalJson(comparedOr(r, schema, e)) ===
    canonicalJson(comparedOr(r, schema, maskCreated(w, peer, t, expected, actual)))
  );
}

/** Lean's World.peerMessage. */
function peerMessage(w: World, i: number, peer: string, fits: (m: Message) => boolean): number {
  const found = w.messages.flatMap((m, k) => (m.status === "inFlight" && m.sender === peer && fits(m) ? [k] : []));
  const oldest = found.filter(
    (k) => !found.some((j) => j < k && sameChannel(w.messages[j] as Message, w.messages[k] as Message)),
  );
  if (oldest.length === 1) return oldest[0] as number;
  if (oldest.length === 0)
    return reportedHere({ kind: "Report.unpairedPeerLine", definition: null, data: { scenarioLine: i, peer } });
  return reportedHere({
    kind: "Report.ambiguousPeerLine",
    definition: null,
    data: { scenarioLine: i, peer, candidates: oldest.map((k) => describe(w.messages[k] as Message)) },
  });
}

/** Lean's World.deliverCarried. */
function deliverCarried(w: World, i: number, k: number): void {
  w.carried.push([i, k]);
  const m = w.messages[k];
  if (m === undefined) return;
  const before = stateOf(w, m.receiver)?.lines.length ?? 0;
  deliver(w, { type: "line", index: i }, k);
  if (m.body.type === "command" || m.body.type === "query" || m.body.type === "subscribe")
    recordSent(w, i, m.receiver, before);
}

/** Lean's World.deliverInOrder. */
function deliverInOrder(w: World, i: number, k: number): void {
  const m = w.messages[k];
  if (m === undefined) return;
  const earlier = w.messages.slice(0, k).find((n) => n.status === "inFlight" && sameChannel(n, m));
  if (earlier !== undefined)
    reportedHere({
      kind: "Report.overtaking",
      definition: null,
      data: { scenarioLine: i, message: describe(m), earlier: describe(earlier) },
    });
  deliverCarried(w, i, k);
}

/** Lean's World.requestId. */
function requestId(w: World, i: number, fact: Fact): string {
  if (fact.type === "line") {
    const s = sentBy(w, fact.index);
    return s === undefined
      ? reportedHere({
          kind: "Report.unresolvedReference",
          definition: null,
          data: { scenarioLine: i, fact: json(fact) },
        })
      : s.id;
  }
  const m = w.messages[messageOf(w, i, fact)] as Message;
  return receivedId(m.sender, m.id);
}

/** Lean's offeredAt. */
function offeredAt(r: Processing, o: Opened, control: string, payload: unknown): boolean {
  const parsed = r.functions.parse({ kind: "control", screen: ref(r.st, o.chart), control }, payload);
  if (parsed instanceof Failed || "error" in parsed) return false;
  try {
    const found = accepting(r, o.chart, control, parsed);
    return "top" in found && found.top.resource === o.resource;
  } catch (error) {
    if (error instanceof Halt) return false;
    throw error;
  }
}

/** Lean's fireTo. */
function fireTo(time: Temporal.Instant, order: readonly DeadlineId[]): (r: Processing) => void {
  return (r) => {
    const s = r.state;
    s.deadlineOrder = order;
    s.tieOrderRequired = true;
    fireDue(r, time);
    checkOrderUsed(r);
    if (Temporal.Instant.compare(time, s.now) > 0) s.now = time;
    s.tieOrderRequired = false;
    writeInput(s, { dir: "in", type: "time" });
  };
}

function wrongRole(i: number, service: string): never {
  return reportedHere({ kind: "Report.wrongRole", definition: null, data: { scenarioLine: i, service } });
}

const notInFlight = (i: number, m: Message): never =>
  reportedHere({ kind: "Report.notInFlight", definition: null, data: { scenarioLine: i, message: describe(m) } });

/** Lean's World.line. */
function line(w: World, own: string, lines: readonly Line[], expectations: readonly Expectation[], i: number, l: Line) {
  const origin = { type: "line", index: i } as const;
  switch (l.type) {
    case "request": {
      if (l.peer === undefined) return clientRequest(w, i, l.kind, l.target, l.input, l.sameIdAs);
      const peer = l.peer;
      const role = w.roles.get(peer);
      if (role === "external") return clientRequest(w, i, l.kind, l.target, l.input, l.sameIdAs);
      if (role !== "run") return wrongRole(i, peer);
      const v = fill(w, i, l.input);
      const name = traceNameOfRef(l.target, peer);
      const r = processingOf(w, peer) as Processing;
      const k = peerMessage(w, i, peer, (m) => {
        const b = m.body;
        if (b.type !== l.kind || b.name !== name) return false;
        return m.receiver === l.target.service && sameValue(w, r, inputSchema(r.st, name), peer, l.input, v, b.input);
      });
      return deliverInOrder(w, i, k);
    }
    case "unsubscribe": {
      const s = sentBy(w, l.subscription);
      if (s === undefined)
        return reportedHere({
          kind: "Report.unresolvedReference",
          definition: null,
          data: { scenarioLine: i, fact: { type: "line", index: l.subscription } },
        });
      const direct = () => act(w, origin, s.receiver, (r) => endSubscription(r, { to: s.id }));
      if (l.peer === undefined) return direct();
      const peer = l.peer;
      const role = w.roles.get(peer);
      if (role === "external") return direct();
      if (role !== "run") return wrongRole(i, peer);
      const k = peerMessage(
        w,
        i,
        peer,
        (m) => m.receiver === s.receiver && m.body.type === "unsubscribe" && receivedId(peer, m.body.to) === s.id,
      );
      return deliverInOrder(w, i, k);
    }
    case "resend": {
      const original = lines[l.line];
      if (original?.type !== "request" || original.peer !== undefined)
        return reportedHere({
          kind: "Report.unresolvedReference",
          definition: null,
          data: { scenarioLine: i, fact: { type: "line", index: l.line } },
        });
      return clientRequest(w, i, original.kind, original.target, original.input, l.line);
    }
    case "operate": {
      const o = screenOf(w, i, l.screen);
      if (w.roles.get(o.service) !== "own") return wrongRole(i, o.service);
      const v = fill(w, i, l.payload);
      const s = stateOf(w, o.service);
      const top = s === undefined ? undefined : topOf(s, o.chart);
      if (top?.kind === "ok" && top.instance.resource !== o.resource)
        return reportedHere({
          kind: "Report.unoperableScreen",
          definition: null,
          data: { scenarioLine: i, screen: o.resource },
        });
      return act(w, origin, o.service, (r) => operate(r, o.chart, l.control, v));
    }
    case "look": {
      const o = screenOf(w, i, l.screen);
      const r = processingOf(w, o.service);
      if (r === undefined) return wrongRole(i, o.service);
      expectations.forEach((e, k) => {
        if (e.type !== "offered" || e.look !== i || stopped(w)) return;
        const v = e.payload === undefined ? {} : fill(w, i, e.payload);
        w.looked.push([k, offeredAt(r, o, e.control, v)]);
      });
      return;
    }
    case "answer": {
      const k = messageOf(w, i, l.request);
      const m = w.messages[k] as Message;
      if (m.receiver !== l.peer)
        return reportedHere({
          kind: "Report.unresolvedReference",
          definition: null,
          data: { scenarioLine: i, fact: json(l.request) },
        });
      const to = receivedId(m.sender, m.id);
      const role = w.roles.get(l.peer);
      if (role === "external") {
        if (m.status !== "inFlight") return notInFlight(i, m);
        const v = fill(w, i, l.answer);
        const a = answerOfValue(v);
        if (a === undefined)
          return reportedHere({
            kind: "Report.malformedValue",
            definition: null,
            data: { scenarioLine: i, value: json(v) },
          });
        m.status = "delivered";
        w.messages.push(answerMessage(l.peer, m.sender, to, a, origin));
        return deliverCarried(w, i, w.messages.length - 1);
      }
      if (role === "run") {
        const j = w.messages.findIndex(
          (n) =>
            n.status === "inFlight" &&
            n.sender === l.peer &&
            n.receiver === m.sender &&
            n.body.type === "answer" &&
            n.body.to === to,
        );
        if (j < 0)
          return reportedHere({
            kind: "Report.unpairedPeerLine",
            definition: null,
            data: { scenarioLine: i, peer: l.peer },
          });
        const v = fill(w, i, l.answer);
        const reply = w.messages[j] as Message;
        const actual: Answer = reply.body.type === "answer" ? reply.body.answer : { result: "accepted" };
        const r = processingOf(w, l.peer) as Processing;
        const t = targetOf(m);
        const peerTarget = t === undefined ? "" : traceNameOfRef(t, l.peer);
        const written = markCreated(l.answer, v);
        const shown = comparedAnswerValue(r, peerTarget, maskCreated(w, l.peer, l.answer, v, actual));
        const expected = comparedAnswerValue(r, peerTarget, written);
        if (canonicalJson(expected) !== canonicalJson(shown))
          reportTo(w, {
            kind: "Report.differentPeerAnswer",
            definition: null,
            data: { scenarioLine: i, expected: json(expected), actual: json(shown) },
          });
        return deliverInOrder(w, i, j);
      }
      return wrongRole(i, l.peer);
    }
    case "emit": {
      const resultId = l.resultOf === undefined ? undefined : requestId(w, i, l.resultOf);
      const v = fill(w, i, l.payload);
      const role = w.roles.get(l.peer);
      if (role === "external") {
        const key = `${l.peer}.${l.event.name}`;
        const n = (w.emitted.get(key) ?? 0) + 1;
        w.emitted.set(key, n);
        const id = `${l.event.name}#${n}`;
        const body: TraceLine = {
          time: "",
          dir: "out",
          type: "event",
          id,
          name: l.event.name,
          payload: v,
          ...(resultId === undefined ? {} : { resultOf: resultId }),
        };
        for (const [r, p] of w.participants) {
          if (stopped(w) || !p.processing.st.received.includes(traceNameOfRef(l.event, r))) continue;
          w.messages.push({ sender: l.peer, receiver: r, id, body, origin, channel: resultId, status: "inFlight" });
          deliverCarried(w, i, w.messages.length - 1);
        }
        return;
      }
      if (role === "run") {
        const peer = l.peer;
        const r = processingOf(w, peer) as Processing;
        const k = peerMessage(w, i, peer, (m) => {
          const b = m.body;
          if (b.type !== "event") return false;
          const event = refOfTraceName(peer, b.name);
          return (
            m.receiver === own &&
            event.service === l.event.service &&
            event.name === l.event.name &&
            b.resultOf === resultId &&
            sameValue(w, r, payloadSchema(r.st, b.name), peer, l.payload, v, b.payload)
          );
        });
        return deliverInOrder(w, i, k);
      }
      return wrongRole(i, l.peer);
    }
    case "leaveUnanswered": {
      const k = messageOf(w, i, l.request);
      const m = w.messages[k] as Message;
      if (w.roles.get(l.peer) !== "external" || m.receiver !== l.peer) return wrongRole(i, l.peer);
      if (m.status !== "inFlight") return notInFlight(i, m);
      m.status = "unanswered";
      return;
    }
    case "deliver": {
      const k = messageOf(w, i, l.message);
      const m = w.messages[k] as Message;
      if (m.status !== "inFlight") return notInFlight(i, m);
      if (!running(w.roles.get(m.receiver))) return wrongRole(i, m.receiver);
      return deliverInOrder(w, i, k);
    }
    case "redeliver": {
      const k = messageOf(w, i, l.message);
      const m = w.messages[k] as Message;
      if (m.status !== "delivered")
        return reportedHere({
          kind: "Report.notDelivered",
          definition: null,
          data: { scenarioLine: i, message: describe(m) },
        });
      return deliverCarried(w, i, k);
    }
    case "lose": {
      const k = messageOf(w, i, l.message);
      const m = w.messages[k] as Message;
      if (m.status !== "inFlight") return notInFlight(i, m);
      m.status = "lost";
      return;
    }
    case "fail": {
      const k = messageOf(w, i, l.message);
      const m = w.messages[k] as Message;
      if (m.status !== "inFlight") return notInFlight(i, m);
      if (m.body.type !== "command" && m.body.type !== "query" && m.body.type !== "subscribe")
        return reportedHere({
          kind: "Report.unfailable",
          definition: null,
          data: { scenarioLine: i, message: describe(m) },
        });
      m.status = "lost";
      const unavailable: Answer = { result: "rejected", rejection: { kind: "unavailable" } };
      w.messages.push(answerMessage(m.receiver, m.sender, receivedId(m.sender, m.id), unavailable, origin));
      return deliverCarried(w, i, w.messages.length - 1);
    }
    case "inFlight": {
      const m = w.messages[messageOf(w, i, l.message)] as Message;
      w.inFlight.push([i, m.sender, m.receiver, m.channel]);
      return;
    }
    case "at": {
      const time = Temporal.Instant.from(l.time);
      if (Temporal.Instant.compare(time, w.now) <= 0)
        return reportedHere({
          kind: "Report.notLater",
          definition: null,
          data: { scenarioLine: i, at: time.toString(), now: w.now.toString() },
        });
      const unknown = l.order.find((e) => !running(w.roles.get(e.service)));
      if (unknown !== undefined) return wrongRole(i, unknown.service);
      for (const service of w.participants.keys()) {
        if (stopped(w)) break;
        const order = l.order.filter((e) => e.service === service).map((e) => e.deadline);
        act(w, origin, service, fireTo(time, order));
      }
      w.now = time;
      return;
    }
    case "restart":
      return act(w, origin, own, restart);
  }
}

/** The answer `a` to the request `to` that `sender` sends to `receiver`, in flight, as line `origin` carries it. */
function answerMessage(
  sender: string,
  receiver: string,
  to: string,
  a: Answer,
  origin: { readonly type: "line"; readonly index: number },
): Message {
  const id = `answer:${to}`;
  return {
    sender,
    receiver,
    id,
    body: { time: "", dir: "out", type: "answer", id, to, answer: a },
    origin,
    channel: to,
    status: "inFlight",
  };
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

type InFlight = World["inFlight"][number];

/** Lean's covers. */
const covers = ([, a, b, c]: InFlight, m: Message): boolean =>
  c === m.channel && ((a === m.sender && b === m.receiver) || (a === m.receiver && b === m.sender));

/** Lean's World.checkEnd. */
function checkEnd(w: World): void {
  const left = w.messages.filter((m) => m.status === "inFlight");
  for (const m of left)
    if (!w.inFlight.some((entry) => covers(entry, m)))
      reportTo(w, { kind: "Report.leftInFlight", definition: null, data: { message: describe(m) } });
  for (const entry of w.inFlight)
    if (!left.some((m) => covers(entry, m)))
      reportTo(w, { kind: "Report.unusedInFlight", definition: null, data: { scenarioLine: entry[0] } });
}

/** Lean's bag. */
const bag = (vs: readonly unknown[]): unknown[] =>
  vs.toSorted((a, b) => byCodePoint(canonicalJson(a), canonicalJson(b)));

/** Lean's World.compared. */
function compared(
  w: World,
  own: string,
  lines: readonly Line[],
  k: number,
  e: Expectation,
): readonly [unknown, unknown] | undefined {
  const r = processingOf(w, own);
  if (r === undefined) return undefined;
  const st = r.st;
  switch (e.type) {
    case "answered": {
      const s = sentBy(w, e.line);
      if (s === undefined)
        return reportedHere({
          kind: "Report.unresolvedReference",
          definition: null,
          data: { scenarioLine: e.line, fact: { type: "line", index: e.line } },
        });
      const request = stateOf(w, s.receiver)?.lines[s.position];
      const target =
        request?.type === "command" || request?.type === "query" || request?.type === "subscribe" ? request.name : "";
      const rr = processingOf(w, s.receiver) as Processing;
      const actual = answersOf(w, s).map((a) => comparedAnswer(rr, target, a));
      const expected = e.answers.map((t) => comparedAnswerValue(rr, target, fill(w, e.line, t)));
      return [expected, actual];
    }
    case "emitted": {
      const actual = spanLines(w, { type: "line", index: e.line }, own).flatMap((l) =>
        l.dir === "out" && l.type === "event" && contractsListing(st.structure, refOf(st, l.name)).length > 0
          ? [{ event: refOf(st, l.name), payload: comparedOr(r, payloadSchema(st, l.name), l.payload) }]
          : [],
      );
      const filled = e.events.map((ev) => [ev.event, fill(w, e.line, ev.payload)] as const);
      const expected = filled.map(([event, v]) => ({
        event,
        payload: comparedOr(r, payloadSchema(st, traceNameOfRef(event, own)), v),
      }));
      return [bag(expected), bag(actual)];
    }
    case "requested": {
      const span = spanLines(w, { type: "line", index: e.line }, own);
      const actualEnds = span.flatMap((l) => (l.dir === "out" && l.type === "unsubscribe" ? [l.to] : []));
      const actual = span.flatMap((l) =>
        l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe")
          ? [{ kind: l.type, target: refOf(st, l.name), input: comparedOr(r, inputSchema(st, l.name), l.input) }]
          : [],
      );
      const filled = e.requests.map((q) => [q, fill(w, e.line, q.input)] as const);
      const expectedEnds = e.ends.map((f) => w.messages[messageOf(w, e.line, f)]?.id ?? "");
      const expected = filled.map(([q, v]) => ({
        kind: q.kind,
        target: q.target,
        input: comparedOr(r, inputSchema(st, traceNameOfRef(q.target, own)), v),
      }));
      return [
        { requests: bag(expected), ends: bag(expectedEnds) },
        { requests: bag(actual), ends: bag(actualEnds) },
      ];
    }
    case "offered": {
      if (lines[e.look]?.type !== "look")
        return reportedHere({
          kind: "Report.notLook",
          definition: null,
          data: { expectation: k, scenarioLine: e.look },
        });
      const found = w.looked.find(([j]) => j === k);
      return found === undefined ? undefined : [e.offered, found[1]];
    }
  }
}

/** Lean's World.expect. */
function expect(w: World, own: string, lines: readonly Line[], expectations: readonly Expectation[]): void {
  expectations.forEach((e, k) => {
    try {
      const both = compared(w, own, lines, k, e);
      if (both === undefined) return;
      const [expected, actual] = both;
      if (canonicalJson(expected) !== canonicalJson(actual))
        noteTo(w, {
          kind: "Report.unmetExpectation",
          definition: null,
          data: { expectation: k, expected: json(expected), actual: json(actual) },
        });
    } catch (error) {
      if (!(error instanceof Reported)) throw error;
      noteTo(w, error.report);
    }
  });
}

/** Lean's simulate. */
export function simulate(structure: Structure, w: World, sc: Scenario): World {
  given(w, structure, sc);
  if (w.reports.length > 0) return w;
  for (const service of w.participants.keys()) if (!stopped(w)) act(w, { type: "begin" }, service, begin);
  sc.lines.forEach((l, i) => {
    if (stopped(w)) return;
    try {
      line(w, sc.service, sc.lines, sc.expectations, i, l);
    } catch (error) {
      if (!(error instanceof Reported)) throw error;
      reportTo(w, error.report);
    }
  });
  if (stopped(w)) return w;
  checkEnd(w);
  expect(w, sc.service, sc.lines, sc.expectations);
  return w;
}
