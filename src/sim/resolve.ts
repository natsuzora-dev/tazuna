import type { DefinitionRef } from "../data/definitionRef.ts";
import type { InvalidScenario } from "../data/invalidScenario.generated.ts";
import type { Fact, Origin, Template, ValueRef } from "../data/scenario.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import { canonicalJson, type Json, mapStrings, overlay, stringsOf } from "../data/values.ts";
import type { Schema } from "../service/basic.ts";
import { Failed } from "../service/functions.ts";
import { chartOf } from "../service/instance.ts";
import type { Line, LineBody } from "../service/message.ts";
import { created } from "../service/state.ts";
import { describe, type Message, type Opened, running, type Sent, sameOrigin, stateOf, type World } from "./network.ts";

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

/** Lean's comparedOr. */
function comparedOr(w: World, service: string, schema: Schema, v: unknown): unknown {
  const r = w.services.get(service)?.processing;
  if (r === undefined) return v;
  const c = r.functions.unordered(schema, v);
  return c instanceof Failed ? v : c;
}

/** Lean's picks. */
const picks = (w: World, service: string, schema: Schema, pick: unknown, v: unknown): boolean =>
  pick === undefined ||
  canonicalJson(comparedOr(w, service, schema, overlay(v, pick))) === canonicalJson(comparedOr(w, service, schema, v));

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

const sameRef = (a: DefinitionRef | undefined, b: DefinitionRef): boolean =>
  a !== undefined && a.service === b.service && a.name === b.name;

/** Lean's Message.target?. */
export function targetOf(m: Message): DefinitionRef | undefined {
  const b = m.body;
  return b.type === "command" || b.type === "query" || b.type === "subscribe" ? b.target : undefined;
}

const eventOf = (m: Message): DefinitionRef | undefined => (m.body.type === "event" ? m.body.event : undefined);

export const sentBy = (w: World, line: number): Sent | undefined => w.sent.find((s) => s.line === line);

const unresolved = (i: number, fact: Fact): never =>
  reported({
    kind: "InvalidScenario.unresolvedReference",
    definition: null,
    data: { scenarioLine: i, fact: json(fact) },
  });

/** Lean's World.only. */
function only(w: World, i: number, fact: Fact, found: readonly number[]): number {
  if (found.length === 1) return found[0] as number;
  if (found.length === 0) return unresolved(i, fact);
  return reported({
    kind: "InvalidScenario.ambiguousReference",
    definition: null,
    data: {
      scenarioLine: i,
      fact: json(fact),
      candidates: found.flatMap((k) => {
        const m = w.messages[k];
        return m === undefined ? [] : [describe(m)];
      }),
    },
  });
}

/** Lean's Fact.group?. */
export const groupOf = (fact: Extract<Fact, { type: "requests" }>): Fact => ({ ...fact, handle: 0 });

/** Lean's World.requestsOf. */
export function requestsOf(w: World, i: number, fact: Fact): number[] {
  if (fact.type !== "requests") return unresolved(i, fact);
  const pick = fact.input === undefined ? undefined : fill(w, i, fact.input);
  const found = w.messages.flatMap((m, k) => {
    if (!(sameOrigin(m.origin, fact.origin) && m.body.type === fact.kind && sameRef(targetOf(m), fact.target)))
      return [];
    const schema = schemaOf(w, m);
    const v = valueOfLine(m.body);
    if (schema === undefined || v === undefined || !picks(w, schema[0], schema[1], pick, v)) return [];
    return [[k, canonicalJson(comparedOr(w, schema[0], schema[1], v))] as const];
  });
  if (!found.every(([, c]) => c === found[0]?.[1]))
    return reported({
      kind: "InvalidScenario.ambiguousReference",
      definition: null,
      data: {
        scenarioLine: i,
        fact: json(fact),
        candidates: found.flatMap(([k]) => {
          const m = w.messages[k];
          return m === undefined ? [] : [describe(m)];
        }),
      },
    });
  return found.map(([k]) => k);
}

/** Lean's World.messageOf. */
export function messageOf(w: World, i: number, fact: Fact): number {
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
  switch (fact.type) {
    case "request":
      return only(
        w,
        i,
        fact,
        picked(
          (m) => sameOrigin(m.origin, fact.origin) && m.body.type === fact.kind && sameRef(targetOf(m), fact.target),
          fact.input,
        ),
      );
    case "requests": {
      const found = requestsOf(w, i, fact);
      const key = canonicalJson(groupOf(fact) as Json);
      const place = w.assignments.find(([g]) => canonicalJson(g as Json) === key)?.[1][fact.handle] ?? fact.handle;
      const k = found[place];
      return k === undefined ? unresolved(i, fact) : k;
    }
    case "event":
      return only(
        w,
        i,
        fact,
        picked(
          (m) =>
            sameOrigin(m.origin, fact.origin) &&
            sameRef(eventOf(m), fact.event) &&
            (fact.receiver === undefined || fact.receiver === m.receiver),
          fact.payload,
        ),
      );
    case "answer": {
      const s = sentBy(w, fact.to);
      if (s === undefined) return unresolved(i, fact);
      return only(
        w,
        i,
        fact,
        matching(
          (m) =>
            sameOrigin(m.origin, fact.origin) &&
            m.sender === s.receiver &&
            m.body.type === "answer" &&
            m.body.to === s.id,
        ),
      );
    }
    case "end": {
      const sub = w.messages[messageOf(w, i, fact.subscription)];
      if (sub === undefined) return unresolved(i, fact);
      return only(
        w,
        i,
        fact,
        matching(
          (m) =>
            sameOrigin(m.origin, fact.origin) &&
            m.sender === sub.sender &&
            m.receiver === sub.receiver &&
            m.body.type === "unsubscribe" &&
            m.body.to === sub.id,
        ),
      );
    }
    case "line":
      return only(
        w,
        i,
        fact,
        w.carried.flatMap(([l, k]) => (l === fact.index ? [k] : [])),
      );
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
  const next = lines.findIndex((l, n) => n > s.position && l.dir === "in" && l.id === s.id);
  return lines.flatMap((l, n) =>
    n > s.position && (next < 0 || n < next) && l.type === "answer" && l.dir === "out" && l.to === s.id
      ? [l.answer]
      : [],
  );
}

/** Lean's Answer.output?. */
const outputOf = (a: Answer | undefined): unknown =>
  a === undefined || a.result === "rejected" ? undefined : a.output;

/** Lean's World.partOf. */
function partOf(w: World, i: number, fact: Fact, part: Part): unknown {
  const missing = (): never =>
    reported({ kind: "InvalidScenario.missingOutput", definition: null, data: { scenarioLine: i, fact: json(fact) } });
  const present = (v: unknown) => (v === undefined ? missing() : v);
  const viaMessage = () => {
    const m = w.messages[messageOf(w, i, fact)];
    if (m === undefined) return missing();
    if (m.body.type === "answer" && part === "output") return present(outputOf(m.body.answer));
    if (part === "input") return present(valueOfLine(m.body));
    const received = (stateOf(w, m.sender)?.lines ?? []).find(
      (l) => l.dir === "in" && l.type === "answer" && l.to === m.id,
    );
    return present(received?.type === "answer" ? outputOf(received.answer) : undefined);
  };
  if (fact.type === "line") {
    const s = sentBy(w, fact.index);
    if (s === undefined) return viaMessage();
    if (part === "input") {
      const l = stateOf(w, s.receiver)?.lines[s.position];
      return present(l === undefined ? undefined : valueOfLine(l));
    }
    return present(outputOf(answersOf(w, s)[0]));
  }
  if (fact.type === "answer" && part === "output") {
    const s = sentBy(w, fact.to);
    if (s === undefined) return unresolved(i, fact);
    const given = spanLines(w, fact.origin, s.receiver).flatMap((l) =>
      l.dir === "out" && l.type === "answer" && l.to === s.id ? [l.answer] : [],
    );
    if (given.length === 1) return present(outputOf(given[0]));
    if (given.length === 0) return unresolved(i, fact);
    return reported({
      kind: "InvalidScenario.ambiguousReference",
      definition: null,
      data: { scenarioLine: i, fact: json(fact), candidates: given.map(json) },
    });
  }
  return viaMessage();
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
