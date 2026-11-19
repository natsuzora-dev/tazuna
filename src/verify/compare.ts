import {
  andThen,
  type Binding,
  bind,
  bindString,
  binds,
  bound,
  distinctBy,
  domainPart,
  emptyBinding,
  expand,
  imageOf,
  type Matches,
  matchValue,
  sameBinding,
  sameSet,
  stringPairs,
  type Values,
  valuePart,
} from "../data/binding.ts";
import { Bag, comparable, comparableAnswer, type KeyPositions, orderFree, Ref, Runs } from "../data/canonical.ts";
import { bindingLimit } from "../data/limits.generated.ts";
import type { Mismatch } from "../data/mismatch.generated.ts";
import { Subscriptions } from "../data/subscriptions.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import {
  type Bindings,
  contentOf,
  type FileLine,
  nameOf,
  operationParts,
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
import type { Spec } from "../load/load.ts";
import { keyPositions } from "../load/schemas.ts";
import { definitionOfTraceName, refOfDefinition } from "../load/traceName.ts";
import { contractsListing } from "../spec/structure.ts";
import { byLine, type Found, lineSchema } from "./lines.ts";

/** Returns the key positions of a shape, each with its entity as `<service>/<name>`, the domain of its values. */
export function keyPositionsOf(spec: Spec): (shape: Shape | undefined) => KeyPositions | undefined {
  const known = new WeakMap<Shape, KeyPositions>();
  return (shape) => {
    if (shape === undefined) return undefined;
    const found = known.get(shape);
    if (found !== undefined) return found;
    const keys = new Map(
      keyPositions(shape).map(({ path, entity }) => {
        const ref = refOfDefinition(spec, entity);
        return [JSON.stringify(path), `${ref.service}/${ref.name}`] as const;
      }),
    );
    known.set(shape, keys);
    return keys;
  };
}

/** Lean's readLine: the line with its input, payload or answer output read by its definition's schema. */
export function readLine(spec: Spec, service: string): (l: TraceLine) => TraceLine {
  const outputByRequestId = new Map<string, Shape>();
  const keys = keyPositionsOf(spec);
  return (l) => {
    switch (l.type) {
      case "operation": {
        const { screen, control } = operationParts(l.name);
        const def = definitionOfTraceName(spec, service, screen, "screen");
        const payload = def?.controls?.[control]?.payload;
        return { ...l, payload: comparable(payload, l.payload, keys(payload)) };
      }
      case "answer": {
        const output = outputByRequestId.get(l.to);
        return { ...l, answer: comparableAnswer(l.answer, output, keys(output)) };
      }
      case "event": {
        const def = definitionOfTraceName(spec, service, l.name, "event");
        return def === undefined ? l : { ...l, payload: comparable(def.payload, l.payload, keys(def.payload)) };
      }
      case "command":
      case "query":
      case "subscribe": {
        const def = definitionOfTraceName(spec, service, l.name, l.type === "command" ? "command" : "query");
        if (def === undefined) return l;
        if (def.output !== undefined) outputByRequestId.set(l.id, def.output);
        return { ...l, input: comparable(def.input, l.input, keys(def.input)) };
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
  let open = new Subscriptions<string, undefined>((id) => id);
  return lines.map((l) => {
    if (l?.dir === "in" && l.type === "subscribe") open.subscribe(l.id, undefined);
    else if (l?.dir === "in" && l.type === "unsubscribe") open.unsubscribe(l.to);
    else if (l?.dir === "in" && l.type === "restart") open = new Subscriptions<string, undefined>((id) => id);
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

const isRequestOf = (
  dir: TraceLine["dir"],
  l: TraceLine,
): l is Extract<TraceLine, { readonly type: "command" | "query" | "subscribe" }> =>
  l.dir === dir && (l.type === "command" || l.type === "query" || l.type === "subscribe");

const isOutRequest = (l: TraceLine): boolean => isRequestOf("out", l);

/** Lean's Line.fresh. */
const freshOf = (l: TraceLine): string[] => [
  ...(isOutRequest(l) ? [l.id] : []),
  ...("created" in l ? (l.created ?? []) : []),
];

const nthOf = (l: TraceLine): number | undefined => (l.type === "operation" ? l.nth : undefined);

const sameFields = (s: TraceLine, t: TraceLine): boolean =>
  s.type === t.type && s.dir === t.dir && nameOf(s) === nameOf(t) && nthOf(s) === nthOf(t);

/** Lean's matchContent. */
function matchContent(v: Values, b: Binding, s: TraceLine, t: TraceLine): Matches {
  if (!sameFields(s, t)) return [];
  const ids: Matches = s.dir === "in" || isOutRequest(s) ? bind(v, b, s.id, t.id) : [b];
  const opt = (x: string | undefined, y: string | undefined) => (c: Binding) =>
    x === undefined && y === undefined ? [c] : x !== undefined && y !== undefined ? bind(v, c, x, y) : [];
  return andThen(ids, (c) =>
    andThen(opt(toOf(s), toOf(t))(c), (c) =>
      andThen(opt(resultOf(s), resultOf(t))(c), (c) => {
        const [x, y] = [contentOf(s), contentOf(t)];
        if (x === undefined && y === undefined) return [c];
        return x === undefined || y === undefined ? [] : matchValue(v, c, x, y);
      }),
    ),
  );
}

/** Lean's matchLine. */
const matchLine = (v: Values, b: Binding, s: TraceLine, t: TraceLine): Matches =>
  sameTime(s, t) ? matchContent(v, b, s, t) : [];

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

/** Lean's sameAfter: whether trace line `t` follows the lines that the pairs give those that `s` follows. */
function sameAfter(
  snapshot: readonly Numbered[],
  trace: readonly Numbered[],
  pairs: readonly (readonly [number, number])[],
  s: Numbered,
  t: Numbered,
): boolean {
  const follows = (outs: readonly Numbered[], o: Numbered) => {
    const k = outs.findIndex((x) => x.index === o.index);
    return k < 0 ? [] : mustFollow(outs, outs[k] as Numbered, k);
  };
  const expected = follows(snapshot, s);
  const images = expected.flatMap((n) => pairs.find(([i]) => i === n)?.slice(1) ?? []);
  return images.length === expected.length && sameSet(images, follows(trace, t));
}

type Finding = Mismatch | Uncomparable;

/** Lean's pairChecks: the time, order, and (when `relation`) `after` findings of the way with pairs `pairNumbers`. */
function pairChecks(
  relation: boolean,
  snapshot: readonly Numbered[],
  trace: readonly Numbered[],
  pairNumbers: readonly (readonly [number, number])[],
): Finding[] {
  const at = (xs: readonly Numbered[], i: number) => xs.find((x) => x.index === i);
  const pairs = pairNumbers.flatMap(([i, j]) => {
    const [s, t] = [at(snapshot, i), at(trace, j)];
    return s === undefined || t === undefined ? [] : [[s, t] as const];
  });
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
  const afters = relation
    ? pairs.flatMap(([s, t]): Finding[] =>
        sameAfter(snapshot, trace, pairNumbers, s, t)
          ? []
          : [
              {
                kind: "Mismatch.after",
                definition: null,
                line: t.index,
                data: { subject: subjectOf(t.line), snapshot: s.line.after ?? [], trace: t.line.after ?? [] },
              },
            ],
      )
    : [];
  return [...times, ...orders, ...afters];
}

/** Lean's State: one way of pairing a group's lines so far. */
interface State {
  readonly binding: Binding;
  readonly pairs: readonly (readonly [number, number])[];
}

const usedOf = (st: State): number[] => st.pairs.map(([, j]) => j);

const samePair = (a: readonly [number, number], b: readonly [number, number]) => a[0] === b[0] && a[1] === b[1];

/** Lean's State.same. */
const sameState =
  (named: readonly number[]) =>
  (a: State, b: State): boolean =>
    sameBinding(a.binding, b.binding) &&
    sameSet(usedOf(a), usedOf(b)) &&
    sameSet(
      a.pairs.filter(([i]) => named.includes(i)),
      b.pairs.filter(([i]) => named.includes(i)),
      samePair,
    );

/** Lean's compareGroup. */
function compareGroup(
  set: readonly Binding[],
  v: Values,
  relation: boolean,
  snapshot: readonly Numbered[],
  trace: readonly Numbered[],
  place: number,
): readonly [Finding[], readonly Binding[], boolean] {
  const named = snapshot.flatMap((s, k) => mustFollow(snapshot, s, k));
  const same = sameState(named);
  const over = (s: Numbered): Finding => ({
    kind: "Uncomparable.bindingLimit",
    definition: null,
    line: place,
    data: { subject: subjectOf(s.line), snapshotLine: s.index, limit: bindingLimit },
  });
  const paired = (st: State, s: Numbered, t: Numbered, cs: readonly Binding[]): State[] =>
    cs.map((c) => ({ binding: c, pairs: [...st.pairs, [s.index, t.index] as const] }));
  let states: readonly State[] = set.map((binding) => ({ binding, pairs: [] }));
  const failed: Numbered[] = [];
  for (const s of snapshot) {
    const ways = expand(same, states, (st) => {
      const next: State[] = [];
      for (const t of trace) {
        if (usedOf(st).includes(t.index) || !followsPaired(snapshot)(st.pairs, s.index, t.index)) continue;
        if (relation && !sameAfter(snapshot, trace, st.pairs, s, t)) continue;
        const cs = matchLine(v, st.binding, s.line, t.line);
        if (cs === undefined) return undefined;
        next.push(...paired(st, s, t, cs));
      }
      return next;
    });
    if (ways === undefined) return [[over(s)], set, true];
    if (ways.length === 0) failed.push(s);
    else states = ways;
  }
  const placed: (readonly [Numbered, Numbered | undefined, boolean])[] = [];
  for (const s of failed) {
    const [first] = states;
    const t =
      first === undefined
        ? undefined
        : trace.find(
            (t) => !usedOf(first).includes(t.index) && samePlace(new Map(stringPairs(first.binding)), s.line, t.line),
          );
    if (t === undefined) {
      placed.push([s, undefined, false]);
      continue;
    }
    const free = states.filter((st) => !usedOf(st).includes(t.index));
    const ways = expand(same, free, (st) => {
      const cs = matchContent(v, st.binding, s.line, t.line);
      return cs === undefined ? undefined : paired(st, s, t, cs);
    });
    if (ways === undefined) return [[over(s)], set, true];
    if (ways.length > 0) {
      states = ways;
      placed.push([s, t, true]);
      continue;
    }
    states = free.map((st) => {
      const id = s.line.id;
      const c = isOutRequest(s.line)
        ? (bindString(binds(v, id, t.line.id), st.binding, bound(v.domain(id), id), bound(v.domain(id), t.line.id)) ??
          st.binding)
        : st.binding;
      return { binding: c, pairs: [...st.pairs, [s.index, t.index] as const] };
    });
    placed.push([s, t, false]);
  }
  const [first] = states;
  const used = first === undefined ? [] : usedOf(first);
  const differences = placed.flatMap(([s, t, equal]) =>
    t === undefined ? [missing(s, place)] : equal ? [] : [difference(s.line, t)],
  );
  const unexpectedLines = trace.filter((t) => !used.includes(t.index)).map(unexpected);
  const checks = pairChecks(relation, snapshot, trace, first?.pairs ?? []);
  const kept = states.filter(
    (st) =>
      sameSet(usedOf(st), used) && (checks.length > 0 || pairChecks(relation, snapshot, trace, st.pairs).length === 0),
  );
  return [
    [...differences, ...unexpectedLines, ...checks],
    distinctBy(
      sameBinding,
      kept.map((st) => st.binding),
    ),
    false,
  ];
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
function sameUses(inputs: readonly TraceLine[], σs: readonly string[]): boolean {
  const [u, ...us] = σs.map((σ) => canonicalJson(usesOf(inputs, σ)));
  return u === undefined || us.every((x) => x === u);
}

/** Lean's unrouted. */
function unrouted(
  set: readonly Binding[],
  v: Values,
  inputs: readonly TraceLine[],
  l: TraceLine,
): string[] | undefined {
  for (const σ of stringsOf(useValue(l))) {
    const d = v.domain(σ);
    const images = distinctBy(
      (a, b) => a === b,
      set.map((b) => imageOf(b, bound(d, σ))),
    );
    const standing = distinctBy(
      (a, b) => a === b,
      [
        σ,
        ...set.flatMap((b) =>
          b.pairs.flatMap(([s, t]) => (domainPart(s) === d && images.includes(valuePart(t)) ? [valuePart(s)] : [])),
        ),
      ],
    );
    if (images.length >= 2 && !sameUses(inputs, standing)) return images;
  }
  return undefined;
}

/** Lean's compareGroups. */
function compareGroups(
  lineCount: number,
  internal: (l: TraceLine) => boolean,
  relation: boolean,
  inputs: readonly TraceLine[],
  outs: readonly Numbered[],
  values: Values,
  expected: readonly Group[],
  actual: readonly Group[],
  cut: boolean,
): readonly [Finding[], readonly Binding[]] {
  const found: Finding[] = [];
  let set: readonly Binding[] = [emptyBinding];
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
      const subject = subjectOf(s.line);
      const next = expand(sameBinding, set, (b) => matchLine({ ...values, fresh: new Set() }, b, s.line, t.line));
      if (next === undefined) {
        found.push({
          kind: "Uncomparable.bindingLimit",
          definition: null,
          line: t.index,
          data: { subject, snapshotLine: s.index, limit: bindingLimit },
        });
        break;
      }
      if (next.length === 0) {
        found.push(differentInput(set[0] ?? emptyBinding, s, t));
        break;
      }
      const images = unrouted(set, { ...values, fresh }, inputs, s.line);
      if (images !== undefined) {
        found.push({
          kind: "Uncomparable.ambiguous",
          definition: null,
          line: t.index,
          data: {
            subject,
            snapshotLine: s.index,
            candidates: outs.filter((o) => images.includes(o.line.id)).map((o) => o.index),
          },
        });
        break;
      }
      set = next;
    }
    if (cut && k === actual.length - 1) break;
    const compared = (outs: readonly Numbered[]) => outs.filter((o) => !internal(o.line));
    for (const o of e.outs) for (const v of freshOf(o.line)) fresh.add(v);
    const [groupFound, next, stop] = compareGroup(
      set,
      { ...values, fresh },
      relation,
      compared(e.outs),
      compared(a.outs),
      t?.index ?? 1,
    );
    found.push(...groupFound);
    set = next;
    if (stop) break;
  }
  return [found, set];
}

/**
 * The violations of a comparison, the bindings that agree with every compared line (Lean's Compared.bindings) as `set`,
 * and the pairs of the first as strings, by which the harness gives its next `in` line.
 */
export interface Compared {
  readonly found: Found[];
  readonly set: readonly Binding[];
  readonly first: Bindings;
}

/** Lean's compare: `cut` tells that the trace's last group ends at the line of a finding. */
function compare(
  snapshot: readonly (TraceLine | undefined)[],
  lines: readonly (TraceLine | undefined)[],
  cut: boolean,
  internal: (l: TraceLine) => boolean,
  renamed: (v: Values) => Values,
  relation: boolean,
): readonly [Finding[], readonly Binding[]] {
  const expected = groups(snapshot);
  const actual = groups(lines);
  return compareGroups(
    lines.length,
    internal,
    relation,
    expected.flatMap((g) => (g.input === undefined ? [] : [g.input.line])),
    actual.flatMap((g) => g.outs),
    renamed({ domain: valueDomains(snapshot), fresh: new Set(), image: () => true }),
    expected,
    actual,
    cut,
  );
}

/**
 * Lean's firstDuplicate: the first request line of the direction `dir` that reuses an earlier one's id with another type,
 * name or input. A line with the same ones sends that request again.
 */
function firstDuplicate(dir: TraceLine["dir"], lines: readonly (TraceLine | undefined)[]): Found | undefined {
  const seen = new Map<string, { readonly line: number; readonly request: string }>();
  for (const [i, l] of lines.entries()) {
    if (l === undefined || !isRequestOf(dir, l)) continue;
    const request = JSON.stringify([l.type, l.name, l.input]);
    const first = seen.get(l.id);
    if (first === undefined) seen.set(l.id, { line: i + 1, request });
    else if (first.request !== request)
      return {
        kind: "Uncomparable.duplicateId",
        definition: null,
        line: i + 1,
        data: { id: l.id, firstLine: first.line },
      };
  }
  return undefined;
}

/** Lean's comparedLines: the trace lines that verify checks, and the finding of the line that ends them, if any. */
export function comparedLines(
  dir: TraceLine["dir"],
  trace: readonly FileLine[],
): {
  readonly lines: readonly (TraceLine | undefined)[];
  readonly cut: Found | undefined;
} {
  const { lines, malformed } = untilMalformed(trace);
  const duplicate = firstDuplicate(dir, lines);
  if (duplicate !== undefined) return { lines: lines.slice(0, (duplicate.line ?? 1) - 1), cut: duplicate };
  return { lines, cut: malformed === undefined ? undefined : lineSchema(malformed) };
}

/**
 * Lean's verifyLines: compares the trace lines with the snapshot's lines, and returns the violations and the bindings.
 * A trace line's violation has its 1-based line number in `line`. `renamed` is Lean's: Explore's Settled.renaming, or
 * the identity for verify. `relation` compares the lines' `after` too, as test does for two runs of the simulation.
 */
export function verifyLines(
  spec: Spec,
  service: string,
  snapshot: readonly (TraceLine | undefined)[],
  trace: readonly FileLine[],
  renamed: (v: Values) => Values = (v) => v,
  relation = false,
): Compared {
  const { lines, cut } = comparedLines("out", trace);
  const read = readLine(spec, service);
  const expected = snapshot.map((l) => l && read(l));
  const actual = withoutRepeatedAnswers(lines.map((l) => l && read(l)));
  const [found, set] = compare(expected, actual, cut !== undefined, internalEvent(spec, service), renamed, relation);
  const [first] = set;
  return {
    found: [...found, ...(cut === undefined ? [] : [cut])],
    set,
    first: first === undefined ? new Map() : new Map(stringPairs(first)),
  };
}

/** Compares the trace with the snapshot's lines. A trace line's violation has its 1-based line number in `line`. */
export function compareTrace(
  spec: Spec,
  service: string,
  snapshot: readonly (TraceLine | undefined)[],
  trace: readonly unknown[],
  renamed: (v: Values) => Values = (v) => v,
): Compared {
  const compared = verifyLines(spec, service, snapshot, parseFileLines(trace), renamed);
  return { ...compared, found: compared.found.sort(byLine) };
}

/** Lean's DiffTest compareOf: compares two runs of the simulation, their `after` included, sorted by line. */
export function compareRuns(
  spec: Spec,
  service: string,
  snapshot: readonly TraceLine[],
  run: readonly TraceLine[],
  renamed: (v: Values) => Values,
): Compared {
  const compared = verifyLines(spec, service, snapshot, run, renamed, true);
  return { ...compared, found: compared.found.sort(byLine) };
}
