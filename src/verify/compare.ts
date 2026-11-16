import { Bag, comparable, comparableAnswer, orderFree, Runs } from "../data/canonical.ts";
import type { Mismatch } from "../data/mismatch.generated.ts";
import { Subscriptions } from "../data/subscriptions.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import {
  type Bindings,
  contentOf,
  type FileLine,
  nameOf,
  parseFileLines,
  renamed,
  resultOf,
  sameTime,
  subjectOf,
  toOf,
  untilMalformed,
} from "../data/trace.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import { canonicalJson, type Json, plain, type Shape } from "../data/values.ts";
import type { Spec } from "../load/load.ts";
import { definitionOfTraceName, refOfDefinition } from "../load/traceName.ts";
import { contractsListing } from "../syntax/structure.ts";
import { byLine, type Found, lineSchema } from "./lines.ts";

/** Lean's readLine: the line with its input, payload or answer output read by its definition's schema. */
function readLine(spec: Spec, service: string): (l: TraceLine) => TraceLine {
  const outputByRequestId = new Map<string, Shape>();
  return (l) => {
    switch (l.type) {
      case "operation":
      case "unacceptedOperation": {
        const [screen, control = ""] = l.name.split(".");
        const def = definitionOfTraceName(spec, service, screen, "screen");
        return { ...l, payload: comparable(def?.controls?.[control]?.payload, l.payload) };
      }
      case "answer":
        return { ...l, answer: comparableAnswer(l.answer, outputByRequestId.get(l.to)) };
      case "event": {
        const def = definitionOfTraceName(spec, service, l.name, "event");
        return def === undefined ? l : { ...l, payload: comparable(def.payload, l.payload) };
      }
      case "command":
      case "query":
      case "subscribe": {
        const def = definitionOfTraceName(spec, service, l.name, l.type === "command" ? "command" : "query");
        if (def === undefined) return l;
        if (def.output !== undefined) outputByRequestId.set(l.id, def.output);
        return { ...l, input: comparable(def.input, l.input) };
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
type Match = Bindings | "ambiguous" | undefined;

/** Lean's bindString. */
function bindString(fresh: ReadonlySet<string>, b: Bindings, s: string, t: string): Bindings | undefined {
  const bound = b.get(s);
  if (bound !== undefined) return bound === t ? b : undefined;
  if (fresh.has(s)) return [...b.values()].includes(t) ? undefined : new Map([...b, [s, t]]);
  return s === t ? b : undefined;
}

interface Paired {
  readonly pairs: readonly (readonly [number, number])[];
  readonly bindings: Bindings;
  readonly ambiguous: readonly number[];
  readonly unmatched: readonly number[];
  readonly extra: readonly number[];
}

const sameBindings = (a: Bindings, b: Bindings): boolean =>
  a.size === b.size && [...a].every(([k, v]) => b.get(k) === v);

/** Lean's pairUp. */
function pairUp<A, B>(
  test: (b: Bindings, s: A, t: B) => Match,
  start: Bindings,
  left: readonly (readonly [number, A])[],
  right: readonly (readonly [number, B])[],
): Paired {
  const candidates = (b: Bindings, rs: readonly (readonly [number, B])[], s: A) => {
    const cs: [number, Bindings][] = [];
    let ambiguous = false;
    for (const [j, t] of rs) {
      const m = test(b, s, t);
      if (m === "ambiguous") ambiguous = true;
      else if (m !== undefined) cs.push([j, m]);
    }
    return { cs, ambiguous };
  };
  let b = start;
  let ls = left;
  let rs = right;
  const pairs: (readonly [number, number])[] = [];
  for (let fuel = left.length; fuel > 0; fuel -= 1) {
    let step: readonly [number, number, Bindings] | undefined;
    for (const [i, s] of ls) {
      const { cs, ambiguous } = candidates(b, rs, s);
      const [first] = cs;
      if (ambiguous || first === undefined) continue;
      if (cs.every(([, c]) => sameBindings(c, first[1]))) {
        step = [i, first[0], first[1]];
        break;
      }
    }
    if (step === undefined) break;
    const [i, j, next] = step;
    b = next;
    ls = ls.filter(([k]) => k !== i);
    rs = rs.filter(([k]) => k !== j);
    pairs.push([i, j]);
  }
  const rest = ls.map(([i, s]) => {
    const { cs, ambiguous } = candidates(b, rs, s);
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
  v !== null && typeof v === "object" && !Array.isArray(v) && !(v instanceof Bag) && !(v instanceof Runs);

/** Lean's matchValue. */
function matchValue(fresh: ReadonlySet<string>, b: Bindings, s: unknown, t: unknown): Match {
  if (typeof s === "string" && typeof t === "string") return bindString(fresh, b, s, t);
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

function matchList(fresh: ReadonlySet<string>, b: Bindings, xs: readonly unknown[], ys: readonly unknown[]): Match {
  if (xs.length !== ys.length) return undefined;
  let m: Match = b;
  for (const [i, x] of xs.entries()) {
    if (m === undefined || m === "ambiguous") return m;
    m = matchValue(fresh, m, x, ys[i]);
  }
  return m;
}

function matchBag(fresh: ReadonlySet<string>, b: Bindings, xs: readonly unknown[], ys: readonly unknown[]): Match {
  const p = pairUp(
    (b, x: unknown, y: unknown) => matchValue(fresh, b, x, y),
    b,
    xs.map((x, i) => [i, x] as const),
    ys.map((y, i) => [i, y] as const),
  );
  if (p.ambiguous.length > 0) return "ambiguous";
  return p.unmatched.length === 0 ? p.bindings : undefined;
}

const and = (m: Match, f: (b: Bindings) => Match): Match => (m === undefined || m === "ambiguous" ? m : f(m));

const isOutRequest = (l: TraceLine): boolean =>
  l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe");

/** Lean's Line.fresh. */
const freshOf = (l: TraceLine): string[] => [
  ...(isOutRequest(l) ? [l.id] : []),
  ...("created" in l ? (l.created ?? []) : []),
];

const sameFields = (s: TraceLine, t: TraceLine): boolean =>
  s.type === t.type && s.dir === t.dir && nameOf(s) === nameOf(t);

/** Lean's matchLine. */
function matchLine(fresh: ReadonlySet<string>, b: Bindings, s: TraceLine, t: TraceLine): Match {
  if (!sameFields(s, t)) return undefined;
  const ids = s.dir === "in" || isOutRequest(s) ? bindString(fresh, b, s.id, t.id) : b;
  const opt = (x: string | undefined, y: string | undefined) => (b: Bindings) =>
    x === undefined && y === undefined
      ? b
      : x !== undefined && y !== undefined
        ? bindString(fresh, b, x, y)
        : undefined;
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
  if (s.type === "operation" || s.type === "unacceptedOperation")
    return { kind: "Mismatch.operation", definition: null, line, data };
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

type Finding = Mismatch | Uncomparable;

/** Lean's compareGroup. */
function compareGroup(
  start: Bindings,
  fresh: ReadonlySet<string>,
  snapshot: readonly Numbered[],
  trace: readonly Numbered[],
  place: number,
): readonly [Finding[], Bindings, boolean] {
  const p = pairUp(
    (b, s: Numbered, t: Numbered) => matchLine(fresh, b, s.line, t.line),
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
  const placed: (readonly [Numbered, Numbered | undefined])[] = [];
  for (const i of p.unmatched) {
    const s = at(snapshot, i);
    if (s === undefined) continue;
    const t = trace.filter((t) => extra.includes(t.index)).find((t) => samePlace(b, s.line, t.line));
    if (t === undefined) placed.push([s, undefined]);
    else {
      if (isOutRequest(s.line)) b = bindString(fresh, b, s.line.id, t.line.id) ?? b;
      placed.push([s, t]);
      extra = extra.filter((j) => j !== t.index);
    }
  }
  const differences = placed.map(([s, t]) => (t === undefined ? missing(s, place) : difference(s.line, t)));
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
const differentInput = (b: Bindings, s: Numbered, t: Numbered): Finding => ({
  kind: "Uncomparable.differentInput",
  definition: null,
  line: t.index,
  data: { snapshotLine: s.index, snapshot: renamed(b, lineValue(s.line)), trace: lineValue(t.line) },
});

/** Lean's compareGroups. */
function compareGroups(
  lineCount: number,
  internal: (l: TraceLine) => boolean,
  expected: readonly Group[],
  actual: readonly Group[],
  cut: boolean,
): readonly [Finding[], Bindings] {
  const found: Finding[] = [];
  let b: Bindings = new Map();
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
      const m = matchLine(new Set(), b, s.line, t.line);
      if (m === undefined || m === "ambiguous" || !sameTime(s.line, t.line)) {
        found.push(differentInput(b, s, t));
        break;
      }
      b = m;
    }
    if (cut && k === actual.length - 1) break;
    const compared = (outs: readonly Numbered[]) => outs.filter((o) => !internal(o.line));
    for (const o of e.outs) for (const v of freshOf(o.line)) fresh.add(v);
    const [groupFound, next, stop] = compareGroup(b, fresh, compared(e.outs), compared(a.outs), t?.index ?? 1);
    found.push(...groupFound);
    b = next;
    if (stop) break;
  }
  return [found, b];
}

/** The violations of a comparison, and the bindings that it ends with. */
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
): readonly [Finding[], Bindings] {
  const [found, bindings] = compareGroups(
    lines.length,
    internal,
    groups(snapshot),
    groups(lines),
    malformed !== undefined,
  );
  return [found, bindings];
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
  const [found, bindings] = compare(expected, actual, malformed?.lineNumber, internalEvent(spec, service));
  return { found: [...found, ...(malformed === undefined ? [] : [lineSchema(malformed)])], bindings };
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
