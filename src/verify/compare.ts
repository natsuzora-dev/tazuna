import { Bag, comparable, comparableAnswer, orderFree, Ref, type RefEntity, Runs } from "../data/canonical.ts";
import type { Mismatch } from "../data/mismatch.generated.ts";
import { Subscriptions } from "../data/subscriptions.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import {
  type Bindings,
  contentOf,
  type FileLine,
  nameOf,
  parseFileLines,
  resultOf,
  sameTime,
  subjectOf,
  substituted,
  toOf,
  untilMalformed,
} from "../data/trace.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import { canonicalJson, type Json, mapStrings, plain, type Shape, stringsOf } from "../data/values.ts";
import { refTarget } from "../dsl/entity.ts";
import type { Spec } from "../load/load.ts";
import { definitionOfTraceName, refOfDefinition } from "../load/traceName.ts";
import { contractsListing } from "../syntax/structure.ts";
import {
  type Binding,
  bindSlots,
  bindString,
  bound,
  emptyBinding,
  refine,
  refineSlots,
  type Slot,
  sameSlot,
  singletons,
  stringPairs,
  valuePart,
} from "./binding.ts";
import { byLine, type Found, lineSchema } from "./lines.ts";

/** Names the entity of a key reference as `<service>/<name>`, the domain of its values. */
export function refEntityOf(spec: Spec): RefEntity {
  return (schema) => {
    const target = refTarget(schema);
    if (target === undefined) return undefined;
    const ref = refOfDefinition(spec, target);
    return `${ref.service}/${ref.name}`;
  };
}

/** Lean's readLine: the line with its input, payload or answer output read by its definition's schema. */
function readLine(spec: Spec, service: string): (l: TraceLine) => TraceLine {
  const outputByRequestId = new Map<string, Shape>();
  const refEntity = refEntityOf(spec);
  return (l) => {
    switch (l.type) {
      case "operation": {
        const [screen, control = ""] = l.name.split(".");
        const def = definitionOfTraceName(spec, service, screen, "screen");
        return { ...l, payload: comparable(def?.controls?.[control]?.payload, l.payload, refEntity) };
      }
      case "answer":
        return { ...l, answer: comparableAnswer(l.answer, outputByRequestId.get(l.to), refEntity) };
      case "event": {
        const def = definitionOfTraceName(spec, service, l.name, "event");
        return def === undefined ? l : { ...l, payload: comparable(def.payload, l.payload, refEntity) };
      }
      case "command":
      case "query":
      case "subscribe": {
        const def = definitionOfTraceName(spec, service, l.name, l.type === "command" ? "command" : "query");
        if (def === undefined) return l;
        if (def.output !== undefined) outputByRequestId.set(l.id, def.output);
        return { ...l, input: comparable(def.input, l.input, refEntity) };
      }
      case "unsubscribe":
      case "time":
      case "restart":
        return l;
    }
  };
}

/** Lean's withoutRepeatedAnswers. */
function withoutRepeatedAnswers(lines: readonly (TraceLine | undefined)[]): (TraceLine | undefined)[] {
  const open = new Subscriptions<undefined>();
  return lines.map((l) => {
    if (l?.dir === "in" && l.type === "subscribe") open.subscribe(l.id, undefined);
    else if (l?.dir === "in" && l.type === "unsubscribe") open.unsubscribe(l.to);
    else if (l?.dir === "out" && l.type === "answer" && open.repeats(l.to, l.answer)) return undefined;
    return l;
  });
}

/** Lean's internalEvent. */
function internalEvent(spec: Spec, service: string): (l: TraceLine) => boolean {
  return (l) => {
    if (l.dir !== "out" || l.type !== "event") return false;
    const def = definitionOfTraceName(spec, service, l.name, "event");
    return def !== undefined && contractsListing(spec.structure, refOfDefinition(spec, def)).length === 0;
  };
}

interface Numbered {
  readonly line: TraceLine;
  /** The 1-based line number. */
  readonly index: number;
}

interface Group {
  readonly input: Numbered | undefined;
  readonly outs: readonly Numbered[];
}

/** Lean's groups. */
function groups(lines: readonly (TraceLine | undefined)[]): Group[] {
  const result: { input: Numbered | undefined; outs: Numbered[] }[] = [{ input: undefined, outs: [] }];
  lines.forEach((line, i) => {
    if (line === undefined) return;
    if (line.dir === "out") result.at(-1)?.outs.push({ line, index: i + 1 });
    else result.push({ input: { line, index: i + 1 }, outs: [] });
  });
  return result;
}

/** Lean's Match: `undefined` is `differ`. */
type Match = Binding | "ambiguous" | undefined;

interface Paired {
  readonly pairs: readonly (readonly [number, number])[];
  readonly bindings: Binding;
  readonly ambiguous: readonly number[];
  readonly unmatched: readonly number[];
  readonly extra: readonly number[];
}

/** Lean's newPair. */
function newPair(b: Binding, b2: Binding): readonly [string, string] | undefined {
  const before = singletons(b.slots);
  const gives = ([s, t]: readonly [string, string]) => {
    const slots = bindSlots(b.slots, s, t);
    return (
      slots !== undefined && slots.length === b2.slots.length && slots.every((k, i) => sameSlot(k, b2.slots[i] as Slot))
    );
  };
  return singletons(b2.slots)
    .filter(([s, t]) => !before.some(([x, y]) => x === s && y === t))
    .find(gives);
}

/** Lean's allSame. */
const allSame = <T>(xs: readonly T[]): T | undefined => {
  const [x] = xs;
  return x !== undefined && xs.every((y) => y === x) ? x : undefined;
};

/** Lean's sameSlots. */
const sameSlots = (a: Binding, b: Binding): boolean =>
  a.slots.length === b.slots.length &&
  (a.slots.every((k, i) => sameSlot(k, b.slots[i] as Slot)) ||
    a.slots.every((k) => b.slots.some((k2) => sameSlot(k, k2))));

/** Lean's pairUp. */
function pairUp<A, B>(
  test: (b: Binding, s: A, t: B) => Match,
  allowed: (pairs: readonly (readonly [number, number])[], i: number, j: number) => boolean,
  start: Binding,
  left: readonly (readonly [number, A])[],
  right: readonly (readonly [number, B])[],
): Paired {
  type Candidates = { readonly cs: (readonly [number, Binding])[]; readonly ambiguous: boolean };
  const candidates = (
    b: Binding,
    pairs: readonly (readonly [number, number])[],
    rs: readonly (readonly [number, B])[],
    i: number,
    s: A,
  ): Candidates => {
    const cs: (readonly [number, Binding])[] = [];
    let ambiguous = false;
    for (const [j, t] of rs) {
      if (!allowed(pairs, i, j)) continue;
      const m = test(b, s, t);
      if (m === "ambiguous") ambiguous = true;
      else if (m !== undefined) cs.push([j, m]);
    }
    return { cs, ambiguous };
  };
  type Step = readonly [readonly (readonly [number, number])[], Binding];
  const determined = (
    b: Binding,
    pairs: readonly (readonly [number, number])[],
    ls: readonly (readonly [number, A])[],
    rs: readonly (readonly [number, B])[],
  ): Step | undefined => {
    for (const [i, s] of ls) {
      const { cs, ambiguous } = candidates(b, pairs, rs, i, s);
      const [first] = cs;
      if (ambiguous || first === undefined) continue;
      if (cs.every(([, c]) => sameSlots(c, first[1]))) return [[[i, first[0]]], first[1]];
    }
    return undefined;
  };
  const block = (
    b: Binding,
    pairs: readonly (readonly [number, number])[],
    ls: readonly (readonly [number, A])[],
    rs: readonly (readonly [number, B])[],
  ): Step | undefined => {
    for (const [i, s] of ls) {
      const { cs, ambiguous } = candidates(b, pairs, rs, i, s);
      if (ambiguous || cs.length < 2) continue;
      const js = cs.map(([j]) => j);
      const group = ls.flatMap(([k, x]) => {
        const c = candidates(b, pairs, rs, k, x);
        return !c.ambiguous && c.cs.length === js.length && c.cs.every(([j], n) => j === js[n])
          ? [[k, c.cs] as const]
          : [];
      });
      if (group.length !== js.length) continue;
      const rows = group.map(([, cx]) => cx.map(([, c]) => newPair(b, c)));
      if (rows.some((row) => row.some((p) => p === undefined))) continue;
      const full = rows as (readonly [string, string])[][];
      const σs = full.map((row) => allSame(row.map(([σ]) => σ)));
      const τs = js.map((_, n) => allSame(full.map((row) => row[n]?.[1] ?? bound("", ""))));
      if (σs.some((σ) => σ === undefined) || τs.some((τ) => τ === undefined)) continue;
      const slots = refineSlots(b.slots, σs as string[], τs as string[]);
      const refined = slots === undefined ? undefined : refine(b, slots);
      if (refined === undefined) continue;
      return [group.map(([k], n) => [k, js[n] as number] as const), refined];
    }
    return undefined;
  };
  let b = start;
  let ls = left;
  let rs = right;
  const pairs: (readonly [number, number])[] = [];
  for (let fuel = left.length; fuel > 0; fuel -= 1) {
    const step = determined(b, pairs, ls, rs) ?? block(b, pairs, ls, rs);
    if (step === undefined) break;
    const [added, next] = step;
    b = next;
    ls = ls.filter(([k]) => !added.some(([i]) => i === k));
    rs = rs.filter(([k]) => !added.some(([, j]) => j === k));
    pairs.push(...added);
  }
  const rest = ls.map(([i, s]) => {
    const { cs, ambiguous } = candidates(b, pairs, rs, i, s);
    return { i, isAmbiguous: ambiguous || cs.length >= 2 };
  });
  return {
    pairs,
    bindings: b,
    ambiguous: rest.filter((r) => r.isAmbiguous).map((r) => r.i),
    unmatched: rest.filter((r) => !r.isAmbiguous).map((r) => r.i),
    extra: rs.map(([j]) => j),
  };
}

const isPlainObject = (v: unknown): v is Record<string, unknown> =>
  v !== null &&
  typeof v === "object" &&
  !Array.isArray(v) &&
  !(v instanceof Bag) &&
  !(v instanceof Runs) &&
  !(v instanceof Ref);

/** Lean's Values: the domain of each snapshot value (valueDomains), and the fresh values so far. */
interface Values {
  readonly domain: (s: string) => string;
  readonly fresh: ReadonlySet<string>;
}

/** Lean's Values.bind. */
const bind = (v: Values, b: Binding, s: string, t: string): Match =>
  bindString(v.fresh.has(s), b, bound(v.domain(s), s), bound(v.domain(s), t));

/** Lean's matchValue. */
function matchValue(fresh: Values, b: Binding, s: unknown, t: unknown): Match {
  if (typeof s === "string" && typeof t === "string") return bind(fresh, b, s, t);
  if (s instanceof Ref && t instanceof Ref) return bind(fresh, b, s.value, t.value);
  if (s instanceof Bag && t instanceof Bag)
    return s.items.length === t.items.length ? matchBag(fresh, b, s.items, t.items) : undefined;
  if (s instanceof Runs && t instanceof Runs) return matchList(fresh, b, s.runs, t.runs);
  if (Array.isArray(s) && Array.isArray(t)) return matchList(fresh, b, s, t);
  if (isPlainObject(s) && isPlainObject(t)) {
    const ks = Object.keys(s);
    const kt = Object.keys(t);
    if (ks.length !== kt.length || !ks.every((k) => kt.includes(k))) return undefined;
    let m: Match = b;
    for (const k of ks) {
      if (m === undefined || m === "ambiguous") return m;
      m = matchValue(fresh, m, s[k], t[k]);
    }
    return m;
  }
  const leaf = (v: unknown) => v === null || typeof v !== "object";
  return leaf(s) && leaf(t) && typeof s !== "string" && typeof t !== "string" && s === t ? b : undefined;
}

function matchList(fresh: Values, b: Binding, xs: readonly unknown[], ys: readonly unknown[]): Match {
  if (xs.length !== ys.length) return undefined;
  let m: Match = b;
  for (const [i, x] of xs.entries()) {
    if (m === undefined || m === "ambiguous") return m;
    m = matchValue(fresh, m, x, ys[i]);
  }
  return m;
}

function matchBag(fresh: Values, b: Binding, xs: readonly unknown[], ys: readonly unknown[]): Match {
  const p = pairUp(
    (b, x: unknown, y: unknown) => matchValue(fresh, b, x, y),
    () => true,
    b,
    xs.map((x, i) => [i, x] as const),
    ys.map((y, i) => [i, y] as const),
  );
  if (p.ambiguous.length > 0) return "ambiguous";
  return p.unmatched.length === 0 ? p.bindings : undefined;
}

const and = (m: Match, f: (b: Binding) => Match): Match => (m === undefined || m === "ambiguous" ? m : f(m));

const isOutRequest = (l: TraceLine): boolean =>
  l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe");

/** Lean's Line.fresh. */
const freshOf = (l: TraceLine): string[] => [
  ...(isOutRequest(l) ? [l.id] : []),
  ...("created" in l ? (l.created ?? []) : []),
];

const sameFields = (s: TraceLine, t: TraceLine): boolean =>
  s.type === t.type && s.dir === t.dir && nameOf(s) === nameOf(t);

/** Lean's matchContent. */
function matchContent(fresh: Values, b: Binding, s: TraceLine, t: TraceLine): Match {
  if (!sameFields(s, t)) return undefined;
  const ids = s.dir === "in" || isOutRequest(s) ? bind(fresh, b, s.id, t.id) : b;
  const opt = (x: string | undefined, y: string | undefined) => (b: Binding) =>
    x === undefined && y === undefined ? b : x !== undefined && y !== undefined ? bind(fresh, b, x, y) : undefined;
  return and(ids, (b) =>
    and(opt(toOf(s), toOf(t))(b), (b) =>
      and(opt(resultOf(s), resultOf(t))(b), (b) => {
        const [x, y] = [contentOf(s), contentOf(t)];
        if (x === undefined && y === undefined) return b;
        return x === undefined || y === undefined ? undefined : matchValue(fresh, b, x, y);
      }),
    ),
  );
}

/** Lean's matchLine. */
const matchLine = (fresh: Values, b: Binding, s: TraceLine, t: TraceLine): Match =>
  sameTime(s, t) ? matchContent(fresh, b, s, t) : undefined;

const json = (value: unknown): Json => plain(value);

/** Lean's samePlace. */
const samePlace = (b: Bindings, s: TraceLine, t: TraceLine): boolean => {
  const to = toOf(s);
  return sameFields(s, t) && (to === undefined ? undefined : (b.get(to) ?? to)) === toOf(t);
};

const key = (value: unknown) => canonicalJson(orderFree(value));

/** Lean's difference. */
function difference(s: TraceLine, t: Numbered): Mismatch {
  const subject = subjectOf(t.line);
  const line = t.index;
  const tl = t.line;
  if (s.type === "answer" && tl.type === "answer") {
    if (s.answer.result === "rejected" && tl.answer.result === "rejected")
      return {
        kind: "Mismatch.rejection",
        definition: null,
        line,
        data: { subject, snapshot: s.answer.rejection.kind, trace: tl.answer.rejection.kind },
      };
    if (s.answer.result !== tl.answer.result)
      return {
        kind: "Mismatch.result",
        definition: null,
        line,
        data: { subject, snapshot: s.answer.result, trace: tl.answer.result },
      };
    return {
      kind: "Mismatch.output",
      definition: null,
      line,
      data: { subject, snapshot: json(s.answer), trace: json(tl.answer) },
    };
  }
  if (s.type === "event" && tl.type === "event") {
    if (key(s.payload) === key(tl.payload))
      return {
        kind: "Mismatch.resultOf",
        definition: null,
        line,
        data: { subject, snapshot: s.resultOf ?? null, trace: tl.resultOf ?? null },
      };
    return {
      kind: "Mismatch.event",
      definition: null,
      line,
      data: { subject, snapshot: json(s.payload), trace: json(tl.payload) },
    };
  }
  const data = { subject, snapshot: json(contentOf(s)), trace: json(contentOf(tl)) };
  if (s.type === "operation") return { kind: "Mismatch.operation", definition: null, line, data };
  return { kind: "Mismatch.request", definition: null, line, data };
}

/** Lean's missing. */
function missing(s: Numbered, place: number): Mismatch {
  const subject = subjectOf(s.line);
  if (s.line.type === "answer")
    return { kind: "Mismatch.missingAnswer", definition: null, line: place, data: { subject, snapshotLine: s.index } };
  const data = { subject, content: json(contentOf(s.line)), snapshotLine: s.index };
  return s.line.type === "subscribe" && s.line.dir === "out"
    ? { kind: "Mismatch.unopenedSubscription", definition: null, line: place, data }
    : { kind: "Mismatch.missingLine", definition: null, line: place, data };
}

/** Lean's unexpected. */
function unexpected(t: Numbered): Mismatch {
  const subject = subjectOf(t.line);
  return t.line.type === "subscribe" && t.line.dir === "out"
    ? {
        kind: "Mismatch.unexpectedSubscription",
        definition: null,
        line: t.index,
        data: { subject, content: json(contentOf(t.line)) },
      }
    : { kind: "Mismatch.unexpectedLine", definition: null, line: t.index, data: { subject } };
}

const earlierWithId = (earlier: readonly Numbered[], id: string): Numbered | undefined =>
  earlier.findLast((o) => o.line.id === id);

/** Lean's mustFollow. */
const mustFollow = (outs: readonly Numbered[], o: Numbered, k: number): number[] =>
  (o.line.after ?? []).flatMap((id) => {
    const earlier = earlierWithId(outs.slice(0, k), id);
    return earlier === undefined ? [] : [earlier.index];
  });

/** Lean's followsPaired. */
const followsPaired =
  (snapshot: readonly Numbered[]) =>
  (pairs: readonly (readonly [number, number])[], i: number, j: number): boolean => {
    const k = snapshot.findIndex((s) => s.index === i);
    const s = snapshot[k];
    if (s === undefined) return true;
    return mustFollow(snapshot, s, k).every((n) => {
      const before = pairs.find(([x]) => x === n)?.[1];
      return before === undefined || before < j;
    });
  };

type Finding = Mismatch | Uncomparable;

/** Lean's compareGroup. */
function compareGroup(
  start: Binding,
  fresh: Values,
  snapshot: readonly Numbered[],
  trace: readonly Numbered[],
  place: number,
): readonly [Finding[], Binding, boolean] {
  const p = pairUp(
    (b, s: Numbered, t: Numbered) => matchLine(fresh, b, s.line, t.line),
    followsPaired(snapshot),
    start,
    snapshot.map((s) => [s.index, s] as const),
    trace.map((t) => [t.index, t] as const),
  );
  const at = (xs: readonly Numbered[], i: number) => xs.find((x) => x.index === i);
  const ambiguous = p.ambiguous.flatMap((i): Finding[] => {
    const s = at(snapshot, i);
    if (s === undefined) return [];
    const candidates = trace
      .filter((t) => !p.pairs.some(([, j]) => j === t.index))
      .filter((t) => matchLine(fresh, p.bindings, s.line, t.line) !== undefined)
      .map((t) => t.index);
    return [
      {
        kind: "Uncomparable.ambiguous",
        definition: null,
        line: candidates[0] ?? place,
        data: { subject: subjectOf(s.line), snapshotLine: s.index, candidates },
      },
    ];
  });
  if (ambiguous.length > 0) return [ambiguous, p.bindings, true];
  let b = p.bindings;
  let extra = [...p.extra];
  const placed: (readonly [Numbered, Numbered | undefined, boolean])[] = [];
  for (const i of p.unmatched) {
    const s = at(snapshot, i);
    if (s === undefined) continue;
    const t = trace
      .filter((t) => extra.includes(t.index))
      .find((t) => samePlace(new Map(stringPairs(b)), s.line, t.line));
    if (t === undefined) placed.push([s, undefined, false]);
    else {
      extra = extra.filter((j) => j !== t.index);
      const m = matchContent(fresh, b, s.line, t.line);
      if (m !== undefined && m !== "ambiguous") {
        b = m;
        placed.push([s, t, true]);
      } else {
        if (isOutRequest(s.line)) {
          const m2 = bind(fresh, b, s.line.id, t.line.id);
          if (m2 !== undefined && m2 !== "ambiguous") b = m2;
        }
        placed.push([s, t, false]);
      }
    }
  }
  const differences = placed.flatMap(([s, t, equal]) =>
    t === undefined ? [missing(s, place)] : equal ? [] : [difference(s.line, t)],
  );
  const unexpectedLines = trace.filter((t) => extra.includes(t.index)).map(unexpected);
  const pairs: (readonly [Numbered, Numbered])[] = [
    ...p.pairs.flatMap(([i, j]) => {
      const [s, t] = [at(snapshot, i), at(trace, j)];
      return s === undefined || t === undefined ? [] : [[s, t] as const];
    }),
    ...placed.flatMap(([s, t]) => (t === undefined ? [] : [[s, t] as const])),
  ];
  const times = pairs.flatMap(([s, t]): Finding[] =>
    sameTime(s.line, t.line)
      ? []
      : [
          {
            kind: "Mismatch.time",
            definition: null,
            line: t.index,
            data: { subject: subjectOf(t.line), snapshot: s.line.time, trace: t.line.time },
          },
        ],
  );
  const orders = snapshot.flatMap((s, k): Finding[] => {
    const t = pairs.find(([x]) => x.index === s.index)?.[1];
    if (t === undefined) return [];
    return mustFollow(snapshot, s, k).flatMap((n): Finding[] => {
      const before = pairs.find(([x]) => x.index === n)?.[1];
      if (before === undefined || before.index < t.index) return [];
      return [
        {
          kind: "Mismatch.lineOrder",
          definition: null,
          line: t.index,
          data: { subject: subjectOf(t.line), before: subjectOf(before.line) },
        },
      ];
    });
  });
  return [[...differences, ...unexpectedLines, ...times, ...orders], b, false];
}

const lineValue = (l: TraceLine): Json => plain(l);

/** Lean's differentInput. */
const differentInput = (b: Binding, s: Numbered, t: Numbered): Finding => ({
  kind: "Uncomparable.differentInput",
  definition: null,
  line: t.index,
  data: {
    snapshotLine: s.index,
    snapshot: substituted(new Map(stringPairs(b)), lineValue(s.line)),
    trace: lineValue(t.line),
  },
});

/** Lean's Line.requestIds. */
const requestIdsOf = (l: TraceLine): string[] => [
  ...(l.type === "command" || l.type === "query" || l.type === "subscribe" ? [l.id] : []),
  ...(toOf(l) === undefined ? [] : [toOf(l) as string]),
  ...(resultOf(l) === undefined ? [] : [resultOf(l) as string]),
];

/** Lean's CValue.keyRefs. */
function keyRefsOf(value: unknown): (readonly [string, string])[] {
  if (value instanceof Ref) return [[value.value, value.entity]];
  if (value instanceof Bag) return value.items.flatMap(keyRefsOf);
  if (value instanceof Runs) return value.runs.flatMap(keyRefsOf);
  if (Array.isArray(value)) return value.flatMap(keyRefsOf);
  if (value !== null && typeof value === "object") return Object.values(value).flatMap(keyRefsOf);
  return [];
}

/** Lean's valueDomains. */
function valueDomains(snapshot: readonly (TraceLine | undefined)[]): (s: string) => string {
  const lines = snapshot.filter((l) => l !== undefined);
  const requests = new Set(lines.flatMap(requestIdsOf));
  const keys = new Map<string, string>();
  for (const [s, entity] of lines.flatMap((l) => keyRefsOf(contentOf(l)))) if (!keys.has(s)) keys.set(s, entity);
  return (s) => (requests.has(s) ? "request" : (keys.get(s) ?? ""));
}

/** Lean's useValue. */
const useValue = (l: TraceLine): Json => {
  const { id: _, ...rest } = lineValue(l) as Record<string, Json>;
  return rest;
};

/** Lean's usesOf. */
const usesOf = (inputs: readonly TraceLine[], σ: string): string[] =>
  inputs
    .filter((l) => stringsOf(useValue(l)).includes(σ))
    .map((l) => canonicalJson(mapStrings(useValue(l), (x) => (x === σ ? "" : x)) as Json));

/** Lean's sameUses. */
function sameUses(inputs: readonly TraceLine[], [σs]: Slot): boolean {
  const [u, ...us] = σs.map((σ) => canonicalJson(usesOf(inputs, valuePart(σ))));
  return u === undefined || us.every((x) => x === u);
}

/** Lean's unevenSlot. */
function unevenSlot(b: Binding, inputs: readonly TraceLine[], l: TraceLine): Slot | undefined {
  const named = stringsOf(useValue(l));
  return b.slots.find(
    (k) => k[0].length >= 2 && k[0].some((σ) => named.includes(valuePart(σ))) && !sameUses(inputs, k),
  );
}

/** Lean's compareGroups. */
function compareGroups(
  lineCount: number,
  internal: (l: TraceLine) => boolean,
  inputs: readonly TraceLine[],
  outs: readonly Numbered[],
  domain: (s: string) => string,
  expected: readonly Group[],
  actual: readonly Group[],
  cut: boolean,
): readonly [Finding[], Binding] {
  const found: Finding[] = [];
  let b: Binding = emptyBinding;
  const fresh = new Set<string>();
  for (let k = 0; k < Math.max(expected.length, actual.length); k += 1) {
    const [e, a] = [expected[k], actual[k]];
    const s = e?.input;
    const t = a?.input;
    if (s !== undefined && t === undefined) {
      found.push({
        kind: "Uncomparable.missingInput",
        definition: null,
        line: lineCount,
        data: { snapshot: lineValue(s.line), snapshotLine: s.index },
      });
      break;
    }
    if (s === undefined && t !== undefined) {
      found.push({
        kind: "Uncomparable.unexpectedInput",
        definition: null,
        line: t.index,
        data: { trace: lineValue(t.line) },
      });
      break;
    }
    if (e === undefined || a === undefined) break;
    if (s !== undefined && t !== undefined) {
      const m = matchLine({ domain, fresh: new Set() }, b, s.line, t.line);
      if (m === undefined || m === "ambiguous") {
        found.push(differentInput(b, s, t));
        break;
      }
      const uneven = unevenSlot(b, inputs, s.line);
      if (uneven !== undefined) {
        found.push({
          kind: "Uncomparable.ambiguous",
          definition: null,
          line: t.index,
          data: {
            subject: subjectOf(s.line),
            snapshotLine: s.index,
            candidates: outs.filter((o) => uneven[1].some((τ) => valuePart(τ) === o.line.id)).map((o) => o.index),
          },
        });
        break;
      }
      b = m;
    }
    if (cut && k === actual.length - 1) break;
    const compared = (outs: readonly Numbered[]) => outs.filter((o) => !internal(o.line));
    for (const o of e.outs) for (const v of freshOf(o.line)) fresh.add(v);
    const [groupFound, next, stop] = compareGroup(
      b,
      { domain, fresh },
      compared(e.outs),
      compared(a.outs),
      t?.index ?? 1,
    );
    found.push(...groupFound);
    b = next;
    if (stop) break;
  }
  return [found, b];
}

/** The violations of a comparison, and the pairs of the binding that it ends with (Lean's Compared.bindings). */
export interface Compared {
  readonly found: Found[];
  readonly bindings: Bindings;
}

/** Lean's compare. */
function compare(
  snapshot: readonly (TraceLine | undefined)[],
  lines: readonly (TraceLine | undefined)[],
  malformed: number | undefined,
  internal: (l: TraceLine) => boolean,
): readonly [Finding[], Binding] {
  const expected = groups(snapshot);
  const actual = groups(lines);
  const [found, binding] = compareGroups(
    lines.length,
    internal,
    expected.flatMap((g) => (g.input === undefined ? [] : [g.input.line])),
    actual.flatMap((g) => g.outs),
    valueDomains(snapshot),
    expected,
    actual,
    malformed !== undefined,
  );
  return [found, binding];
}

/**
 * Lean's verifyLines: compares the trace lines with the snapshot's lines, and returns the violations and the bindings.
 * A trace line's violation has its 1-based line number in `line`.
 */
export function verifyLines(
  spec: Spec,
  service: string,
  snapshot: readonly (TraceLine | undefined)[],
  trace: readonly FileLine[],
): Compared {
  const { lines, malformed } = untilMalformed(trace);
  const read = readLine(spec, service);
  const expected = snapshot.map((l) => l && read(l));
  const actual = withoutRepeatedAnswers(lines.map((l) => l && read(l)));
  const [found, binding] = compare(expected, actual, malformed?.lineNumber, internalEvent(spec, service));
  return {
    found: [...found, ...(malformed === undefined ? [] : [lineSchema(malformed)])],
    bindings: new Map(stringPairs(binding)),
  };
}

/** Compares the trace with the snapshot's lines. A trace line's violation has its 1-based line number in `line`. */
export function compareTrace(
  spec: Spec,
  service: string,
  snapshot: readonly (TraceLine | undefined)[],
  trace: readonly unknown[],
): Compared {
  const { found, bindings } = verifyLines(spec, service, snapshot, parseFileLines(trace));
  return { found: found.sort(byLine), bindings };
}
