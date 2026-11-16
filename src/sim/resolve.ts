import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Report } from "../data/report.generated.ts";
import type { Fact, Template, ValueRef } from "../data/scenario.generated.ts";
import type { Answer, TraceLine } from "../data/trace.generated.ts";
import { canonicalJson, type Json, overlay } from "../data/values.ts";
import { refOfTraceName } from "../syntax/structure.ts";
import { describe, type Message, type Opened, type Sent, sameOrigin, stateOf, type World } from "./network.ts";

/** A report that a line's handle cannot resolve, which the line reports in place of taking place. */
export class Reported extends Error {
  readonly report: Report;
  constructor(report: Report) {
    super(report.kind);
    this.report = report;
  }
}

type Part = ValueRef["part"];

/** The JSON that Lean's ToValue writes of a scenario value, which is JSON already. */
export const json = (v: unknown): Json => v as Json;

function reported(report: Report): never {
  throw new Reported(report);
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

/** Lean's picks. */
const picks = (pick: unknown, v: unknown): boolean =>
  pick === undefined || canonicalJson(overlay(v, pick)) === canonicalJson(v);

/** Lean's LineBody.value?. */
function valueOfLine(l: TraceLine): unknown {
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
  return b.type === "command" || b.type === "query" || b.type === "subscribe"
    ? refOfTraceName(m.sender, b.name)
    : undefined;
}

const eventOf = (m: Message): DefinitionRef | undefined =>
  m.body.type === "event" ? refOfTraceName(m.sender, m.body.name) : undefined;

export const sentBy = (w: World, line: number): Sent | undefined => w.sent.find((s) => s.line === line);

const unresolved = (i: number, fact: Fact): never =>
  reported({ kind: "Report.unresolvedReference", definition: null, data: { scenarioLine: i, fact: json(fact) } });

/** Lean's World.only. */
function only(w: World, i: number, fact: Fact, found: readonly number[]): number {
  if (found.length === 1) return found[0] as number;
  if (found.length === 0) return unresolved(i, fact);
  return reported({
    kind: "Report.ambiguousReference",
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

/** Lean's World.messageOf. */
export function messageOf(w: World, i: number, fact: Fact): number {
  const matching = (p: (m: Message) => boolean) => w.messages.flatMap((m, k) => (p(m) ? [k] : []));
  switch (fact.type) {
    case "request":
      return only(
        w,
        i,
        fact,
        matching(
          (m) =>
            sameOrigin(m.origin, fact.origin) &&
            sameRef(targetOf(m), fact.target) &&
            picks(fact.input, valueOfLine(m.body) ?? null),
        ),
      );
    case "event":
      return only(
        w,
        i,
        fact,
        matching(
          (m) =>
            sameOrigin(m.origin, fact.origin) &&
            sameRef(eventOf(m), fact.event) &&
            picks(fact.payload, valueOfLine(m.body) ?? null) &&
            (fact.receiver === undefined || fact.receiver === m.receiver),
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
    (s) => sameOrigin(s.origin, fact.origin) && s.service === fact.screen.service && s.chart === fact.screen.name,
  );
  if (found.length === 1) return found[0] as Opened;
  if (found.length === 0) return unresolved(i, fact);
  return reported({
    kind: "Report.ambiguousReference",
    definition: null,
    data: { scenarioLine: i, fact, candidates: found.map((s) => s.resource) },
  });
}

/** Lean's lineValue?. */
const lineValue = (lines: readonly TraceLine[], id: string): unknown => {
  for (const l of lines) if (l.dir === "in" && l.id === id) return valueOfLine(l);
  return undefined;
};

/** Lean's firstAnswer?. */
function firstAnswer(lines: readonly TraceLine[], dir: "in" | "out", to: string): Answer | undefined {
  for (const l of lines) if (l.type === "answer" && l.dir === dir && l.to === to) return l.answer;
  return undefined;
}

/** Lean's Answer.output?. */
const outputOf = (a: Answer | undefined): unknown =>
  a === undefined || a.result === "rejected" ? undefined : a.output;

/** Lean's World.partOf. */
function partOf(w: World, i: number, fact: Fact, part: Part): unknown {
  const missing = (): never =>
    reported({ kind: "Report.missingOutput", definition: null, data: { scenarioLine: i, fact: json(fact) } });
  const present = (v: unknown) => (v === undefined ? missing() : v);
  const s = fact.type === "line" ? sentBy(w, fact.index) : undefined;
  if (s !== undefined) {
    const lines = stateOf(w, s.receiver)?.lines ?? [];
    return present(part === "input" ? lineValue(lines, s.id) : outputOf(firstAnswer(lines, "out", s.id)));
  }
  const m = w.messages[messageOf(w, i, fact)];
  if (m === undefined) return missing();
  return present(
    part === "input" ? valueOfLine(m.body) : outputOf(firstAnswer(stateOf(w, m.sender)?.lines ?? [], "in", m.id)),
  );
}

/** Lean's World.observed. */
function observed(w: World, i: number, r: ValueRef): unknown {
  const v = partOf(w, i, r.fact, r.part);
  const x = valueAt(v, r.path);
  if (x === undefined)
    return reported({
      kind: "Report.missingField",
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

/** Lean's createdPaths. */
export const createdPaths = (t: Template): (readonly string[])[] =>
  t.holes.flatMap((h) => (h.fill.type === "created" ? [h.path] : []));

/** Lean's withCreated. */
export function withCreated(paths: readonly (readonly string[])[], expected: unknown, actual: unknown): unknown {
  let v = expected;
  for (const p of paths) {
    const x = valueAt(actual, p);
    if (x !== undefined) v = setValueAt(v, x, p);
  }
  return v;
}
