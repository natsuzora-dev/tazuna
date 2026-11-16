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
import { Halt } from "../service/state.ts";
import { contractsListing, isKeyOf, refOfTraceName, traceNameOfRef } from "../syntax/structure.ts";
import {
  act,
  deliver,
  describe,
  type Message,
  type Opened,
  type Participant,
  type Role,
  reportTo,
  running,
  sameChannel,
  stateOf,
  stopped,
  type World,
} from "./network.ts";
import { missingSingles, receivedId } from "./participant.ts";
import { createdPaths, fill, json, messageOf, Reported, screenOf, sentBy, targetOf, withCreated } from "./resolve.ts";

type RequestType = Extract<Line, { readonly type: "request" }>["kind"];

/** Lean's canonicalOr. */
function canonicalOr(r: Processing, schema: Schema, v: unknown): unknown {
  const c = r.functions.canonical(schema, v);
  return c instanceof Failed ? v : c;
}

const inputSchema = (st: Service, name: string): Schema => ({ kind: "input", definition: refOf(st, name) });
const outputSchema = (st: Service, name: string): Schema => ({ kind: "output", definition: refOf(st, name) });
const payloadSchema = (st: Service, name: string): Schema => ({ kind: "payload", event: refOf(st, name) });

/** Lean's canonicalAnswer. */
function canonicalAnswer(r: Processing, target: string, a: Answer): unknown {
  if (a.result === "accepted" && a.output !== undefined)
    return { result: "accepted", output: canonicalOr(r, outputSchema(r.st, target), a.output) };
  if (a.result === "fulfilled")
    return { result: "fulfilled", output: canonicalOr(r, outputSchema(r.st, target), a.output) };
  return a;
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
    const entity = st.entities.find((e) => !st.singles.includes(e) && isKeyOf(e, x));
    if (entity !== undefined) return [x, entity];
  }
  return undefined;
}

/** Lean's World.recordSent. */
function recordSent(w: World, i: number, service: string, before: number): void {
  const l = (stateOf(w, service)?.lines ?? []).slice(before).find((line) => line.dir === "in");
  if (l !== undefined) w.sent.push({ line: i, receiver: service, id: l.id });
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

/** Lean's sameValue. */
const sameValue = (
  r: Processing,
  schema: Schema,
  created: readonly (readonly string[])[],
  expected: unknown,
  actual: unknown,
): boolean => canonicalJson(canonicalOr(r, schema, withCreated(created, expected, actual))) === canonicalJson(actual);

/** Lean's World.peerMessage. */
function peerMessage(w: World, i: number, peer: string, fits: (m: Message) => boolean): number {
  const found = w.messages.flatMap((m, k) => (m.status === "inFlight" && m.sender === peer && fits(m) ? [k] : []));
  if (found.length === 1) return found[0] as number;
  if (found.length === 0)
    return reportedHere({ kind: "Report.unpairedPeerLine", definition: null, data: { scenarioLine: i, peer } });
  return reportedHere({
    kind: "Report.ambiguousPeerLine",
    definition: null,
    data: { scenarioLine: i, peer, candidates: found.map((k) => describe(w.messages[k] as Message)) },
  });
}

/** Lean's World.deliverCarried. */
function deliverCarried(w: World, i: number, k: number): void {
  w.carried.push([i, k]);
  const m = w.messages[k];
  if (m === undefined) return;
  deliver(w, { type: "line", index: i }, k);
  if (m.body.type === "command" || m.body.type === "query" || m.body.type === "subscribe")
    w.sent.push({ line: i, receiver: m.receiver, id: receivedId(m.sender, m.id) });
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
      if (w.roles.get(peer) !== "run") return wrongRole(i, peer);
      const v = fill(w, i, l.input);
      const name = traceNameOfRef(l.target, peer);
      const r = processingOf(w, peer) as Processing;
      const k = peerMessage(w, i, peer, (m) => {
        const b = m.body;
        if (b.type !== l.kind || b.name !== name) return false;
        return (
          m.receiver === l.target.service && sameValue(r, inputSchema(r.st, name), createdPaths(l.input), v, b.input)
        );
      });
      return deliverCarried(w, i, k);
    }
    case "unsubscribe": {
      const s = sentBy(w, l.subscription);
      if (s === undefined)
        return reportedHere({
          kind: "Report.unresolvedReference",
          definition: null,
          data: { scenarioLine: i, fact: { type: "line", index: l.subscription } },
        });
      if (l.peer === undefined) return act(w, origin, s.receiver, (r) => endSubscription(r, { to: s.id }));
      const peer = l.peer;
      if (w.roles.get(peer) !== "run") return wrongRole(i, peer);
      const k = peerMessage(
        w,
        i,
        peer,
        (m) => m.receiver === s.receiver && m.body.type === "unsubscribe" && receivedId(peer, m.body.to) === s.id,
      );
      return deliverCarried(w, i, k);
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
      const t = targetOf(m);
      const target = t === undefined ? "" : traceNameOfRef(t, m.sender);
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
        const to = receivedId(m.sender, m.id);
        m.status = "delivered";
        w.messages.push({
          sender: l.peer,
          receiver: m.sender,
          id: `answer:${to}`,
          body: { time: "", dir: "out", type: "answer", id: `answer:${to}`, to, answer: a },
          origin,
          channel: to,
          status: "inFlight",
        });
        return deliverCarried(w, i, w.messages.length - 1);
      }
      if (role === "run") {
        const to = receivedId(m.sender, m.id);
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
        const r = processingOf(w, m.sender) as Processing;
        const shown = canonicalAnswer(r, target, actual);
        const written = answerOfValue(withCreated(createdPaths(l.answer), v, shown));
        const expected = written === undefined ? v : canonicalAnswer(r, target, written);
        if (canonicalJson(expected) !== canonicalJson(shown))
          reportTo(w, {
            kind: "Report.differentPeerAnswer",
            definition: null,
            data: { scenarioLine: i, expected: json(expected), actual: json(shown) },
          });
        return deliverCarried(w, i, j);
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
            sameValue(r, payloadSchema(r.st, b.name), createdPaths(l.payload), v, b.payload)
          );
        });
        return deliverCarried(w, i, k);
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
      const earlier = w.messages.slice(0, k).find((n) => n.status === "inFlight" && sameChannel(n, m));
      if (earlier !== undefined)
        return reportedHere({
          kind: "Report.overtaking",
          definition: null,
          data: { scenarioLine: i, message: describe(m), earlier: describe(earlier) },
        });
      return deliverCarried(w, i, k);
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
    case "inFlight": {
      const m = w.messages[messageOf(w, i, l.message)] as Message;
      w.inFlight.push([m.sender, m.receiver, m.channel]);
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
  for (const m of w.messages)
    if (
      m.status === "inFlight" &&
      !w.inFlight.some(([s, r, c]) => s === m.sender && r === m.receiver && c === m.channel)
    )
      reportTo(w, { kind: "Report.leftInFlight", definition: null, data: { message: describe(m) } });
}

/** Lean's bag. */
const bag = (vs: readonly unknown[]): unknown[] =>
  vs.toSorted((a, b) => byCodePoint(canonicalJson(a), canonicalJson(b)));

/** Lean's World.lineSpan. */
function lineSpan(w: World, service: string, at: number): TraceLine[] {
  const lines = stateOf(w, service)?.lines ?? [];
  return w.spans.flatMap((sp) =>
    sp.origin.type === "line" && sp.origin.index === at && sp.service === service ? lines.slice(sp.from, sp.to) : [],
  );
}

/** Lean's World.compared. */
function compared(w: World, own: string, k: number, e: Expectation): readonly [unknown, unknown] | undefined {
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
      const lines = stateOf(w, s.receiver)?.lines ?? [];
      const request = lines.find((l) => l.dir === "in" && l.id === s.id);
      const target =
        request?.type === "command" || request?.type === "query" || request?.type === "subscribe" ? request.name : "";
      const rr = processingOf(w, s.receiver) as Processing;
      const actual = lines.flatMap((l) =>
        l.type === "answer" && l.dir === "out" && l.to === s.id ? [canonicalAnswer(rr, target, l.answer)] : [],
      );
      const filled = e.answers.map((t) => fill(w, e.line, t));
      const expected = filled.map((v) => {
        const a = answerOfValue(v);
        return a === undefined ? v : canonicalAnswer(rr, target, a);
      });
      return [expected, actual];
    }
    case "emitted": {
      const actual = lineSpan(w, own, e.line).flatMap((l) =>
        l.dir === "out" && l.type === "event" && contractsListing(st.structure, refOf(st, l.name)).length > 0
          ? [{ event: refOf(st, l.name), payload: l.payload }]
          : [],
      );
      const filled = e.events.map((ev) => [ev.event, fill(w, e.line, ev.payload)] as const);
      const expected = filled.map(([event, v]) => ({
        event,
        payload: canonicalOr(r, payloadSchema(st, traceNameOfRef(event, own)), v),
      }));
      return [bag(expected), bag(actual)];
    }
    case "requested": {
      const actual = lineSpan(w, own, e.line).flatMap((l) =>
        l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe")
          ? [{ kind: l.type, target: refOf(st, l.name), input: l.input }]
          : [],
      );
      const filled = e.requests.map((q) => [q, fill(w, e.line, q.input)] as const);
      const expected = filled.map(([q, v]) => ({
        kind: q.kind,
        target: q.target,
        input: canonicalOr(r, inputSchema(st, traceNameOfRef(q.target, own)), v),
      }));
      return [bag(expected), bag(actual)];
    }
    case "offered": {
      const found = w.looked.find(([j]) => j === k);
      return found === undefined ? undefined : [e.offered, found[1]];
    }
  }
}

/** Lean's World.expect. */
function expect(w: World, own: string, expectations: readonly Expectation[]): void {
  expectations.forEach((e, k) => {
    if (stopped(w)) return;
    try {
      const both = compared(w, own, k, e);
      if (both === undefined) return;
      const [expected, actual] = both;
      if (canonicalJson(expected) !== canonicalJson(actual))
        reportTo(w, {
          kind: "Report.unmetExpectation",
          definition: null,
          data: { expectation: k, expected: json(expected), actual: json(actual) },
        });
    } catch (error) {
      if (!(error instanceof Reported)) throw error;
      reportTo(w, error.report);
    }
  });
}

/**
 * Lean's World.start: the roles that Given lists, and each running service's processing, which `processingOf` makes
 * with its Given records at the start.
 */
export function start(sc: Scenario, processingFor: (service: string) => Processing): World {
  const now = Temporal.Instant.from(sc.given.start);
  const roles = new Map<string, Role>([
    [sc.service, "own"],
    ...sc.given.peers.map((p) => [p.service, p.role] as const),
  ]);
  const runningServices = [sc.service, ...sc.given.peers.flatMap((p) => (p.role === "run" ? [p.service] : []))];
  const participants = new Map<string, Participant>(
    runningServices.map((service) => {
      const processing = processingFor(service);
      processing.state.now = now;
      return [service, { processing, halted: undefined }];
    }),
  );
  return {
    now,
    roles,
    participants,
    messages: [],
    spans: [],
    opened: [],
    sent: [],
    carried: [],
    inFlight: [],
    emitted: new Map(),
    looked: [],
    reports: [],
    halted: undefined,
  };
}

/** Lean's simulate. */
export function simulate(w: World, sc: Scenario): World {
  for (const [service, p] of w.participants) {
    const [entity] = missingSingles(p.processing.st, p.processing.state.records);
    if (entity !== undefined) {
      reportTo(w, { kind: "Report.missingRecord", definition: null, data: { service, entity } });
      return w;
    }
  }
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
  expect(w, sc.service, sc.expectations);
  return w;
}
