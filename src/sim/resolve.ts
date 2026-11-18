import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { InvalidScenario } from "../data/invalidScenario.generated.ts";
import type { Fact, Origin, Template, ValueRef } from "../data/scenario.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import { canonicalJson, type Json, mapStrings, overlay, stringsOf } from "../data/values.ts";
import type { Schema } from "../service/basic.ts";
import type { Processing } from "../service/chart/queue.ts";
import { Failed } from "../service/functions.ts";
import { chartOf } from "../service/instance.ts";
import { type Line, type LineBody, sameLineId } from "../service/message.ts";
import { created } from "../service/state.ts";
import {
  describe,
  type Message,
  type Opened,
  running,
  type Sent,
  sameChannel,
  sameOrigin,
  stateOf,
  type World,
} from "./network.ts";

/** A violation that a line's handle cannot resolve, which the line reports in place of taking place. */
export class Reported extends Error {
  readonly violation: InvalidScenario;
  constructor(violation: InvalidScenario) {
    super(violation.kind);
    this.violation = violation;
  }
}

type Part = ValueRef["part"];

/** The JSON that Lean's ToValue writes of a scenario value, which is JSON already. */
export const json = (v: unknown): Json => v as Json;

function reported(violation: InvalidScenario): never {
  throw new Reported(violation);
}

const isObject = (v: unknown): v is Record<string, unknown> => v !== null && typeof v === "object" && !Array.isArray(v);

const indexOf = (k: string): number | undefined => (/^[0-9]+$/.test(k) ? Number(k) : undefined);

/** Lean's valueAt?. */
function valueAt(v: unknown, path: readonly string[]): unknown {
  let current = v;
  for (const k of path) {
    if (isObject(current) && Object.hasOwn(current, k)) current = current[k];
    else if (Array.isArray(current)) {
      const i = indexOf(k);
      if (i === undefined || i >= current.length) return undefined;
      current = current[i];
    } else return undefined;
  }
  return current;
}

/** Lean's setValueAt. */
function setValueAt(v: unknown, x: unknown, path: readonly string[]): unknown {
  const [k, ...rest] = path;
  if (k === undefined) return x;
  if (isObject(v))
    return Object.hasOwn(v, k)
      ? Object.fromEntries(Object.entries(v).map(([n, w]) => [n, n === k ? setValueAt(w, x, rest) : w]))
      : { ...v, [k]: setValueAt({}, x, rest) };
  if (Array.isArray(v)) {
    const i = indexOf(k);
    return i === undefined ? v : v.map((w, j) => (j === i ? setValueAt(w, x, rest) : w));
  }
  return { [k]: setValueAt({}, x, rest) };
}

/** Lean's comparedOr; `v` as it is for a service that is not in the world. */
export function comparedOr(r: Processing | undefined, schema: Schema, v: unknown): unknown {
  const c = r?.functions.unordered(schema, v);
  return c === undefined || c instanceof Failed ? v : c;
}

const processingOf = (w: World, service: string): Processing | undefined => w.services.get(service)?.processing;

/** Lean's picks. */
const picks = (w: World, service: string, schema: Schema, pick: unknown, v: unknown): boolean =>
  pick === undefined ||
  canonicalJson(comparedOr(processingOf(w, service), schema, overlay(v, pick))) ===
    canonicalJson(comparedOr(processingOf(w, service), schema, v));

/** Lean's World.schemaOf?. */
function schemaOf(w: World, m: Message): readonly [string, Schema] | undefined {
  const side = running(w.roles.get(m.sender)) ? m.sender : m.receiver;
  if (!w.services.has(side)) return undefined;
  const b = m.body;
  if (b.type === "command" || b.type === "query" || b.type === "subscribe")
    return [side, { kind: "input", definition: b.target }];
  if (b.type === "event") return [side, { kind: "payload", event: b.event }];
  return undefined;
}

/** Lean's LineBody.value?. */
function valueOfLine(l: LineBody): unknown {
  switch (l.type) {
    case "command":
    case "query":
    case "subscribe":
      return l.input;
    case "event":
      return l.payload;
    default:
      return undefined;
  }
}

/** Lean's Message.target?. */
export function targetOf(m: Message): DefinitionRef | undefined {
  const b = m.body;
  return b.type === "command" || b.type === "query" || b.type === "subscribe" ? b.target : undefined;
}

const eventOf = (m: Message): DefinitionRef | undefined => (m.body.type === "event" ? m.body.event : undefined);

/** Lean's World.sentBy: the requests that line `line` sent or delivered, in the order it did. */
export const sentBy = (w: World, line: number): Sent[] => w.sent.filter((s) => s.line === line);

const unresolved = (i: number, fact: Fact): never =>
  reported({
    kind: "InvalidScenario.unresolvedReference",
    definition: null,
    data: { scenarioLine: i, fact: json(fact) },
  });

/** Lean's nonEmpty. */
function nonEmpty<T>(i: number, fact: Fact, found: readonly T[]): readonly T[] {
  return found.length === 0 ? unresolved(i, fact) : found;
}

/** Lean's World.ambiguous. */
const ambiguous = (w: World, i: number, fact: Fact, ks: readonly number[]): never =>
  reported({
    kind: "InvalidScenario.ambiguousReference",
    definition: null,
    data: {
      scenarioLine: i,
      fact: json(fact),
      candidates: ks.flatMap((k) => {
        const m = w.messages[k];
        return m === undefined ? [] : [describe(m)];
      }),
    },
  });

/** Lean's World.comparedContent?. */
function comparedContent(w: World, k: number): string | undefined {
  const m = w.messages[k];
  if (m === undefined) return undefined;
  const v = valueOfLine(m.body);
  if (v === undefined) return undefined;
  const schema = schemaOf(w, m);
  return canonicalJson(schema === undefined ? v : comparedOr(processingOf(w, schema[0]), schema[1], v));
}

/** Lean's World.alikeMessages: equal messages, of those on one channel the oldest in flight or else the first. */
function alikeMessages(w: World, i: number, fact: Fact, found: readonly number[]): number[] {
  const ks = nonEmpty(i, fact, found);
  const keys = ks.map((k) => comparedContent(w, k));
  if (!keys.every((k) => k === keys[0])) ambiguous(w, i, fact, ks);
  const together = (k: number, j: number) => {
    const [a, b] = [w.messages[k], w.messages[j]];
    return a !== undefined && b !== undefined && sameChannel(a, b);
  };
  return ks.filter((k) => {
    const peers = ks.filter((j) => together(k, j));
    return k === (peers.find((j) => w.messages[j]?.status === "inFlight") ?? peers[0] ?? k);
  });
}

/** Lean's World.messagesOf. */
export function messagesOf(w: World, i: number, fact: Fact): number[] {
  const matching = (p: (m: Message) => boolean) => w.messages.flatMap((m, k) => (p(m) ? [k] : []));
  const picked = (p: (m: Message) => boolean, pick: Template | undefined) => {
    const filled = pick === undefined ? undefined : fill(w, i, pick);
    return matching((m) => {
      if (!p(m)) return false;
      const schema = schemaOf(w, m);
      const v = valueOfLine(m.body);
      return schema !== undefined && v !== undefined && picks(w, schema[0], schema[1], filled, v);
    });
  };
  const oneEach = (each: readonly number[][]): number[] => {
    if (each.some((ks) => ks.length > 1)) ambiguous(w, i, fact, each.flat());
    return [...nonEmpty(i, fact, each.flat())];
  };
  switch (fact.type) {
    case "request":
      return alikeMessages(
        w,
        i,
        fact,
        picked(
          (m) =>
            sameOrigin(m.origin, fact.origin) && m.body.type === fact.kind && sameRef(targetOf(m) ?? null, fact.target),
          fact.input,
        ),
      );
    case "event":
      return alikeMessages(
        w,
        i,
        fact,
        picked(
          (m) =>
            sameOrigin(m.origin, fact.origin) &&
            sameRef(eventOf(m) ?? null, fact.event) &&
            (fact.receiver === undefined || fact.receiver === m.receiver),
          fact.payload,
        ),
      );
    case "answer":
      return oneEach(
        sentBy(w, fact.to).map((s) =>
          matching(
            (m) =>
              sameOrigin(m.origin, fact.origin) &&
              m.sender === s.receiver &&
              m.body.type === "answer" &&
              sameLineId(m.body.to, s.id),
          ),
        ),
      );
    case "end": {
      const subs = messagesOf(w, i, fact.subscription).flatMap((k) => {
        const m = w.messages[k];
        return m === undefined ? [] : [m];
      });
      return oneEach(
        subs.map((sub) =>
          matching(
            (m) =>
              sameOrigin(m.origin, fact.origin) &&
              m.sender === sub.sender &&
              m.receiver === sub.receiver &&
              m.body.type === "unsubscribe" &&
              sameLineId(m.body.to, sub.id),
          ),
        ),
      );
    }
    case "line":
      return [
        ...nonEmpty(
          i,
          fact,
          w.carried.flatMap(([l, k]) => (l === fact.index ? [k] : [])),
        ),
      ];
    case "screen":
      return unresolved(i, fact);
  }
}

/** Lean's World.screenOf. */
export function screenOf(w: World, i: number, fact: Fact): Opened {
  if (fact.type !== "screen") return unresolved(i, fact);
  const found = w.opened.filter(
    (s) => sameOrigin(s.origin, fact.origin) && s.service === fact.screen.service && chartOf(s.id) === fact.screen.name,
  );
  if (found.length === 1) return found[0] as Opened;
  if (found.length === 0) return unresolved(i, fact);
  return reported({
    kind: "InvalidScenario.ambiguousReference",
    definition: null,
    data: { scenarioLine: i, fact, candidates: found.map((s) => s.id) },
  });
}

/** Lean's World.spanLines. */
export function spanLines(w: World, origin: Origin, service: string): Line[] {
  const lines = stateOf(w, service)?.lines ?? [];
  return w.spans.flatMap((sp) =>
    sameOrigin(sp.origin, origin) && sp.service === service ? lines.slice(sp.from, sp.to) : [],
  );
}

/** Lean's World.answersOf. */
export function answersOf(w: World, s: Sent): Answer[] {
  const lines = stateOf(w, s.receiver)?.lines ?? [];
  const next = lines.findIndex((l, n) => n > s.position && l.dir === "in" && sameLineId(l.id, s.id));
  return lines.flatMap((l, n) =>
    n > s.position && (next < 0 || n < next) && l.type === "answer" && l.dir === "out" && sameLineId(l.to, s.id)
      ? [l.answer]
      : [],
  );
}

/** Lean's Answer.output?. */
const outputOf = (a: Answer | undefined): unknown =>
  a === undefined || a.result === "rejected" ? undefined : a.output;

/** Lean's alike: the first raw value, when every compared value is equal. */
function alike(i: number, fact: Fact, missing: () => never, values: readonly (readonly [unknown, unknown])[]): unknown {
  const [first, ...rest] = values;
  if (first === undefined) return missing();
  const key = canonicalJson(first[1]);
  if (rest.every(([, c]) => canonicalJson(c) === key)) return first[0];
  return reported({
    kind: "InvalidScenario.ambiguousReference",
    definition: null,
    data: { scenarioLine: i, fact: json(fact), candidates: values.map(([v]) => json(v)) },
  });
}

/** Lean's World.partOf. */
function partOf(w: World, i: number, fact: Fact, part: Part): unknown {
  const missing = (): never =>
    reported({ kind: "InvalidScenario.missingOutput", definition: null, data: { scenarioLine: i, fact: json(fact) } });
  const compared = (side: string, schema: Schema | undefined, v: unknown) =>
    schema === undefined ? v : comparedOr(processingOf(w, side), schema, v);
  const viaMessages = () => {
    const ks = messagesOf(w, i, fact);
    const values = ks.flatMap((k) => {
      const m = w.messages[k];
      if (m === undefined) return [];
      const schema = schemaOf(w, m);
      const side = schema?.[0] ?? m.sender;
      let v: unknown;
      if (m.body.type === "answer" && part === "output") v = outputOf(m.body.answer);
      else if (part === "input") v = valueOfLine(m.body);
      else {
        const received = (stateOf(w, m.sender)?.lines ?? []).find(
          (l) => l.dir === "in" && l.type === "answer" && sameLineId(l.to, m.id),
        );
        v = received?.type === "answer" ? outputOf(received.answer) : undefined;
      }
      const target = targetOf(m);
      const valueSchema: Schema | undefined =
        part === "input" ? schema?.[1] : target === undefined ? undefined : { kind: "output", definition: target };
      return v === undefined ? [] : [[v, compared(side, valueSchema, v)] as const];
    });
    if (values.length !== ks.length) return missing();
    return alike(i, fact, missing, values);
  };
  if (fact.type === "line") {
    const sents = sentBy(w, fact.index);
    if (sents.length === 0) return viaMessages();
    const values = sents.flatMap((s) => {
      const request = stateOf(w, s.receiver)?.lines[s.position];
      const v =
        part === "input" ? (request === undefined ? undefined : valueOfLine(request)) : outputOf(answersOf(w, s)[0]);
      const target =
        request?.type === "command" || request?.type === "query" || request?.type === "subscribe"
          ? request.target
          : undefined;
      const schema: Schema | undefined =
        target === undefined
          ? undefined
          : part === "input"
            ? { kind: "input", definition: target }
            : { kind: "output", definition: target };
      return v === undefined ? [] : [[v, compared(s.receiver, schema, v)] as const];
    });
    if (values.length !== sents.length) return missing();
    return alike(i, fact, missing, values);
  }
  if (fact.type === "answer" && part === "output") {
    const sents = sentBy(w, fact.to);
    if (sents.length === 0) return unresolved(i, fact);
    const each = sents.map((s) =>
      spanLines(w, fact.origin, s.receiver).flatMap((l) =>
        l.dir === "out" && l.type === "answer" && sameLineId(l.to, s.id) ? [l.answer] : [],
      ),
    );
    if (each.some((given) => given.length === 0)) return unresolved(i, fact);
    if (each.some((given) => given.length > 1))
      return reported({
        kind: "InvalidScenario.ambiguousReference",
        definition: null,
        data: { scenarioLine: i, fact: json(fact), candidates: each.flat().map(json) },
      });
    const outputs = each.flat().flatMap((a) => {
      const o = outputOf(a);
      return o === undefined ? [] : [o];
    });
    if (outputs.length !== sents.length) return missing();
    return alike(
      i,
      fact,
      missing,
      outputs.map((o) => [o, o] as const),
    );
  }
  return viaMessages();
}

/** Lean's World.observed. */
function observed(w: World, i: number, r: ValueRef): unknown {
  const v = partOf(w, i, r.fact, r.part);
  const x = valueAt(v, r.path);
  if (x === undefined)
    return reported({
      kind: "InvalidScenario.missingField",
      definition: null,
      data: { scenarioLine: i, path: r.path, value: json(v) },
    });
  return x;
}

/** Lean's World.fill. */
export function fill(w: World, i: number, t: Template): unknown {
  let v: unknown = t.value;
  for (const h of t.holes) if (h.fill.type === "ref") v = setValueAt(v, observed(w, i, h.fill.value), h.path);
  return v;
}

/** Lean's createdMark. */
const createdMark = "<created>";

/** Lean's markCreated. */
export function markCreated(t: Template, v: unknown): unknown {
  let marked = v;
  for (const h of t.holes) if (h.fill.type === "created") marked = setValueAt(marked, createdMark, h.path);
  return marked;
}

/** Lean's World.maskCreated. */
export function maskCreated(w: World, peer: string, t: Template, filled: unknown, actual: unknown): unknown {
  const named = new Set(t.holes.flatMap((h) => (h.fill.type === "ref" ? stringsOf(valueAt(filled, h.path)) : [])));
  const s = stateOf(w, peer);
  const keys = new Set(s === undefined ? [] : created(s).map(([, key]) => key));
  return mapStrings(actual, (x) => (keys.has(x) && !named.has(x) ? createdMark : x));
}
