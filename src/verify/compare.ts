import { alike, Bag, Runs } from "../data/canonical.ts";
import type { Mismatch, Subject, Use } from "../data/mismatch.generated.ts";
import { Subscriptions } from "../data/subscriptions.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import {
  type Bindings,
  contentOf,
  type MalformedLine,
  type NumberedLine,
  nameOf,
  resultOf,
  sameTime,
  steps,
  toOf,
} from "../data/trace.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import { plain } from "../data/values.ts";
import { type Found, lineSchema, resolveAfters } from "./lines.ts";

const json = (value: unknown) => JSON.stringify(value);

const subjectOf = (l: TraceLine): Subject =>
  l.type === "answer" || l.type === "unsubscribe"
    ? { type: l.type, to: l.to }
    : { type: l.type, name: nameOf(l) ?? null, id: l.id ?? null };

/** The number of steps after which a search stops: a window's search, or the search of one pair of `in` lines. */
const searchLimit = 100000;

/** A one-to-one renaming of snapshot values to implementation values, with the lines that bound each value. */
type Renaming = readonly Use[];

const traceOf = (r: Renaming, s: string): string | undefined => r.find((u) => u.snapshot === s)?.trace;

const takes = (r: Renaming, t: string): boolean => r.some((u) => u.trace === t);

/** Returns the renaming with `u`, unless one of its values already stands for another value. */
function bind(r: Renaming, u: Use): Renaming | undefined {
  const t = traceOf(r, u.snapshot);
  if (t !== undefined) return t === u.trace ? r : undefined;
  return takes(r, u.trace) ? undefined : [...r, u];
}

/** Returns `value` with its renamed createKey values replaced by their implementation values, for reports. */
function substitute(r: Renaming, value: unknown): unknown {
  if (typeof value === "string") return traceOf(r, value) ?? value;
  if (value instanceof Bag) return new Bag(value.items.map((v) => substitute(r, v)));
  if (value instanceof Runs) return new Runs(value.runs.map((v) => substitute(r, v) as Bag));
  if (Array.isArray(value)) return value.map((v) => substitute(r, v));
  if (value && typeof value === "object")
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, substitute(r, v)]));
  return value;
}

/** What a search still has to pair. Bag elements pair at trace line `line` and snapshot line `snapshotLine`. */
type Goal =
  | { readonly kind: "out"; readonly s: NumberedLine }
  | { readonly kind: "subscription"; readonly id: string }
  | {
      readonly kind: "bag";
      readonly line: number;
      readonly snapshotLine: number;
      readonly xs: readonly unknown[];
      readonly ys: readonly unknown[];
    };

const isObject = (v: unknown): v is Record<string, unknown> =>
  v !== null && typeof v === "object" && !Array.isArray(v) && !(v instanceof Bag) && !(v instanceof Runs);

const sameKeys = (s: Record<string, unknown>, t: Record<string, unknown>): boolean =>
  json(Object.keys(s).toSorted()) === json(Object.keys(t).toSorted());

type Walked = readonly [Renaming, readonly Goal[]] | undefined;

/**
 * Returns the renaming under which `s` equals `t` apart from the elements of bags, and the bags left to pair. A
 * declared createKey value equals the implementation string that it is renamed to, and other strings equal themselves.
 */
function walk(
  declared: ReadonlySet<string>,
  line: number,
  snapshotLine: number,
  s: unknown,
  t: unknown,
  r: Renaming,
): Walked {
  if (typeof s === "string") {
    if (typeof t !== "string") return undefined;
    if (!declared.has(s)) return t === s ? [r, []] : undefined;
    const bound = bind(r, { snapshot: s, trace: t, line, snapshotLine });
    return bound === undefined ? undefined : [bound, []];
  }
  if (Array.isArray(s))
    return Array.isArray(t) && s.length === t.length ? walkList(declared, line, snapshotLine, s, t, r) : undefined;
  if (s instanceof Runs)
    return t instanceof Runs && s.runs.length === t.runs.length
      ? walkList(declared, line, snapshotLine, s.runs, t.runs, r)
      : undefined;
  if (s instanceof Bag)
    return t instanceof Bag && s.items.length === t.items.length
      ? [r, [{ kind: "bag", line, snapshotLine, xs: s.items, ys: t.items }]]
      : undefined;
  if (isObject(s)) {
    if (!isObject(t) || !sameKeys(s, t)) return undefined;
    return walkList(
      declared,
      line,
      snapshotLine,
      Object.values(s),
      Object.keys(s).map((k) => t[k]),
      r,
    );
  }
  return s === t ? [r, []] : undefined;
}

function walkList(
  declared: ReadonlySet<string>,
  line: number,
  snapshotLine: number,
  xs: readonly unknown[],
  ys: readonly unknown[],
  r: Renaming,
): Walked {
  let renaming = r;
  const goals: Goal[] = [];
  for (const [i, x] of xs.entries()) {
    const walked = walk(declared, line, snapshotLine, x, ys[i], renaming);
    if (walked === undefined) return undefined;
    renaming = walked[0];
    goals.push(...walked[1]);
  }
  return [renaming, goals];
}

/** Two missing values (undefined) are equal, and one missing value is not. */
const walkContent = (
  declared: ReadonlySet<string>,
  line: number,
  snapshotLine: number,
  s: unknown,
  t: unknown,
  r: Renaming,
): Walked =>
  s === undefined || t === undefined ? (s === t ? [r, []] : undefined) : walk(declared, line, snapshotLine, s, t, r);

/**
 * Returns the uses under which `s` equals `t` when each declared createKey value may stand for any string, for
 * reports. Bags pair their elements by backtracking.
 */
function free(
  declared: ReadonlySet<string>,
  line: number,
  snapshotLine: number,
  s: unknown,
  t: unknown,
): readonly Use[] | undefined {
  if (typeof s === "string") {
    if (typeof t !== "string") return undefined;
    if (!declared.has(s)) return t === s ? [] : undefined;
    return [{ snapshot: s, trace: t, line, snapshotLine }];
  }
  if (Array.isArray(s))
    return Array.isArray(t) && s.length === t.length ? freeList(declared, line, snapshotLine, s, t) : undefined;
  if (s instanceof Runs)
    return t instanceof Runs && s.runs.length === t.runs.length
      ? freeList(declared, line, snapshotLine, s.runs, t.runs)
      : undefined;
  if (s instanceof Bag) return t instanceof Bag ? freeBag(declared, line, snapshotLine, s.items, t.items) : undefined;
  if (isObject(s)) {
    if (!isObject(t) || !sameKeys(s, t)) return undefined;
    return freeList(
      declared,
      line,
      snapshotLine,
      Object.values(s),
      Object.keys(s).map((k) => t[k]),
    );
  }
  return s === t ? [] : undefined;
}

function freeList(
  declared: ReadonlySet<string>,
  line: number,
  snapshotLine: number,
  xs: readonly unknown[],
  ys: readonly unknown[],
): readonly Use[] | undefined {
  const uses: Use[] = [];
  for (const [i, x] of xs.entries()) {
    const found = free(declared, line, snapshotLine, x, ys[i]);
    if (found === undefined) return undefined;
    uses.push(...found);
  }
  return uses;
}

function freeBag(
  declared: ReadonlySet<string>,
  line: number,
  snapshotLine: number,
  ss: readonly unknown[],
  ts: readonly unknown[],
): readonly Use[] | undefined {
  if (ss.length !== ts.length) return undefined;
  const [first, ...rest] = ss;
  if (ss.length === 0) return [];
  for (const [i, t] of ts.entries()) {
    const found = free(declared, line, snapshotLine, first, t);
    if (found === undefined) continue;
    const others = freeBag(declared, line, snapshotLine, rest, ts.toSpliced(i, 1));
    if (others !== undefined) return [...found, ...others];
  }
  return undefined;
}

const freeContent = (
  declared: ReadonlySet<string>,
  line: number,
  snapshotLine: number,
  s: unknown,
  t: unknown,
): readonly Use[] | undefined =>
  s === undefined || t === undefined ? (s === t ? [] : undefined) : free(declared, line, snapshotLine, s, t);

/**
 * Alike `out` requests of window `window`, paired by `uses`. Each snapshot id in `snapshot` stands for one of the
 * implementation ids in `trace`, and binds to it when a line names it.
 */
interface Block {
  readonly line: TraceLine;
  readonly window: number;
  readonly snapshot: readonly string[];
  readonly trace: readonly string[];
  readonly uses: readonly Use[];
}

/** The renaming of request, subscription and input ids, and the blocks of alike requests. */
interface Ids {
  readonly bound: Renaming;
  readonly blocks: readonly Block[];
}

const known = (ids: Ids, s: string): boolean =>
  traceOf(ids.bound, s) !== undefined || ids.blocks.some((b) => b.snapshot.includes(s));

const reserved = (ids: Ids, t: string): boolean => takes(ids.bound, t) || ids.blocks.some((b) => b.trace.includes(t));

const erase = (xs: readonly string[], x: string): readonly string[] => {
  const i = xs.indexOf(x);
  return i === -1 ? xs : xs.toSpliced(i, 1);
};

/** Returns the ids with `u` bound. A snapshot id of a block binds only to an implementation id of the same block. */
function use(ids: Ids, u: Use): Ids | undefined {
  const t = traceOf(ids.bound, u.snapshot);
  if (t !== undefined) return t === u.trace ? ids : undefined;
  const block = ids.blocks.find((b) => b.snapshot.includes(u.snapshot));
  if (block === undefined) return reserved(ids, u.trace) ? undefined : { ...ids, bound: [...ids.bound, u] };
  if (!block.trace.includes(u.trace)) return undefined;
  return {
    bound: [...ids.bound, u],
    blocks: ids.blocks.map((b) =>
      b.snapshot.includes(u.snapshot)
        ? { ...b, snapshot: erase(b.snapshot, u.snapshot), trace: erase(b.trace, u.trace) }
        : b,
    ),
  };
}

/** Two missing ids are the same, and one missing id is not. */
const useIds = (
  ids: Ids,
  line: number,
  snapshotLine: number,
  s: string | undefined,
  t: string | undefined,
): Ids | undefined =>
  s === undefined || t === undefined
    ? s === t
      ? ids
      : undefined
    : use(ids, { snapshot: s, trace: t, line, snapshotLine });

/** Returns the ids with a line's own ids bound. A line whose own id is missing on one side binds nothing. */
const useOwn = (
  ids: Ids,
  line: number,
  snapshotLine: number,
  s: string | undefined,
  t: string | undefined,
): Ids | undefined =>
  s === undefined || t === undefined ? ids : use(ids, { snapshot: s, trace: t, line, snapshotLine });

/**
 * Returns the ids with the ids `u` of a paired `out` request `l` in the block of its alike requests of window
 * `window`. An id that is already bound or in a block binds instead.
 */
function join(ids: Ids, window: number, l: TraceLine, u: Use): Ids | undefined {
  if (known(ids, u.snapshot) || reserved(ids, u.trace)) return use(ids, u);
  const i = ids.blocks.findIndex((b) => b.window === window && alike(b.line, l));
  if (i === -1)
    return {
      ...ids,
      blocks: [...ids.blocks, { line: l, window, snapshot: [u.snapshot], trace: [u.trace], uses: [u] }],
    };
  return {
    ...ids,
    blocks: ids.blocks.map((b, k) =>
      k === i ? { ...b, snapshot: [...b.snapshot, u.snapshot], trace: [...b.trace, u.trace], uses: [...b.uses, u] } : b,
    ),
  };
}

/** Returns the uses that bind an id: the bound ids, and the request of each block that has one request. */
const idUsesOf = (ids: Ids): readonly Use[] => [
  ...ids.bound,
  ...ids.blocks.flatMap((b) => (b.uses.length === 1 ? b.uses : [])),
];

const sameUse = (a: Use, b: Use): boolean =>
  a.snapshot === b.snapshot && a.trace === b.trace && a.line === b.line && a.snapshotLine === b.snapshotLine;

/**
 * Returns the groups of connected uses in which a value stands for two values, each in the order of the uses. A
 * snapshot value and an implementation value connect when a use pairs them.
 */
function conflicts(uses: readonly Use[]): (readonly Use[])[] {
  let groups: (readonly Use[])[] = [];
  for (const [k, u] of uses.entries()) {
    if (uses.slice(0, k).some((v) => sameUse(u, v))) continue;
    const touches = (g: readonly Use[]) => g.some((v) => v.snapshot === u.snapshot || v.trace === u.trace);
    const i = groups.findIndex(touches);
    if (i === -1) groups.push([u]);
    else {
      const rest = groups.filter((g) => !touches(g));
      groups = [...rest.slice(0, i), [...groups.filter(touches).flat(), u], ...rest.slice(i)];
    }
  }
  return groups.filter((g) =>
    g.some((u) =>
      g.some(
        (v) => (u.snapshot === v.snapshot && u.trace !== v.trace) || (u.trace === v.trace && u.snapshot !== v.snapshot),
      ),
    ),
  );
}

type Open = Subscriptions<{ readonly line: Extract<TraceLine, { type: "subscribe" }>; readonly at: number }>;

/** What a window's search compares in, besides the pairing. */
interface Scope {
  readonly declared: ReadonlySet<string>;
  readonly window: number;
  readonly traceOut: readonly NumberedLine[];
  readonly openSnapshot: Open;
  readonly openTrace: Open;
}

/** A pairing that a search builds, with the renamings under which the paired lines are equal. */
interface Pairing {
  readonly ids: Ids;
  readonly keys: Renaming;
  readonly pairs: readonly { readonly spec: NumberedLine; readonly trace: NumberedLine }[];
  readonly subscriptions: readonly (readonly [string, string])[];
}

type Outcome =
  | { readonly kind: "paired"; readonly pairing: Pairing }
  | { readonly kind: "unpaired" }
  | { readonly kind: "limited" };

type Frame = readonly [readonly Goal[], Pairing];

/** Returns the elements of `xs` whose key no earlier element has. */
function distinct<T>(key: (x: T) => string, xs: readonly T[]): T[] {
  const seen = new Set<string>();
  return xs.filter((x) => {
    const k = key(x);
    if (seen.has(k)) return false;
    seen.add(k);
    return true;
  });
}

/** The order in which the search pairs lines: requests and lines that create keys, then answers, then the rest. */
const rank = (l: TraceLine): number =>
  l.type === "command" || l.type === "query" || (l.created ?? []).length > 0 ? 0 : l.type === "answer" ? 1 : 2;

const byRank = (ss: readonly NumberedLine[]): NumberedLine[] =>
  [0, 1, 2].flatMap((r) => ss.filter((s) => rank(s.line) === r));

/** The violations of a comparison, and the bindings that it ends with. */
export interface Compared {
  readonly found: Found[];
  readonly bindings: Bindings;
}

/**
 * Compares the snapshot's lines with the trace's lines, and returns the violations and the bindings. `lines` are the
 * trace lines before its first malformed line `malformed`, and the window of that line is not compared. An unknown
 * after of the snapshot orders no line; readSnapshotProblems reports it before the comparison.
 */
export function compare(
  snapshot: readonly (TraceLine | undefined)[],
  lines: readonly (TraceLine | undefined)[],
  malformed: MalformedLine | undefined,
  internal: (l: TraceLine) => boolean,
): Compared {
  const problems: (Mismatch | Uncomparable)[] = [];
  const expected = steps(snapshot);
  const actual = steps(lines);
  const requestsById = new Map(snapshot.flatMap((l) => (l?.id === undefined ? [] : [[l.id, l] as const])));
  let ids: Ids = { bound: [], blocks: [] };
  let keys: Renaming = [];
  let window = 0;
  const declared = new Set<string>();
  const openInSnapshot: Open = new Subscriptions();
  const openInTrace: Open = new Subscriptions();
  const subscriptionIds = new Map<string, Set<string>>();
  const reportedMissing = new Set<string>();
  const reportedUnexpected = new Set<string>();
  const bindings = () => new Map(keys.map((u) => [u.snapshot, u.trace]));
  const { follows } = resolveAfters(snapshot);

  const answersQuery = (to: string) => {
    const request = requestsById.get(to);
    return request?.type === "query" || request?.type === "subscribe";
  };
  const queryAnswer = (l: TraceLine) =>
    l.type !== "answer" ? undefined : l.answer.result === "fulfilled" ? l.answer.output : l.answer;
  const compared = (s: TraceLine, t: TraceLine): readonly [unknown, unknown] =>
    s.type === "answer" && answersQuery(s.to) ? [queryAnswer(s), queryAnswer(t)] : [contentOf(s), contentOf(t)];

  /** Returns whether pairing `s` with `t` keeps the snapshot's `after` order among the pairs. */
  const ordered = (pairs: Pairing["pairs"], s: NumberedLine, t: NumberedLine): boolean =>
    pairs.every(
      (p) =>
        (follows.get(s.at)?.has(p.spec.at) !== true || p.trace.at < t.at) &&
        (follows.get(p.spec.at)?.has(s.at) !== true || t.at < p.trace.at),
    );

  /** Returns the ids of the pairing with `s` paired with `t`: the answered request's ids, or a request's own ids. */
  const pairIds = (sc: Scope, current: Ids, s: NumberedLine, t: NumberedLine): Ids | undefined => {
    if (s.line.type === "answer") return useIds(current, t.at, s.at, s.line.to, toOf(t.line));
    if (s.line.type !== "command" && s.line.type !== "query") return current;
    const [a, b] = [s.line.id, t.line.id];
    if (a === undefined || b === undefined) return current;
    return join(current, sc.window, s.line, { snapshot: a, trace: b, line: t.at, snapshotLine: s.at });
  };

  /** Returns the pairing with `s` paired with `t`, and the bags left to pair, if `t` can stand for `s`. */
  const pairOut = (
    sc: Scope,
    p: Pairing,
    s: NumberedLine,
    t: NumberedLine,
  ): readonly [Pairing, readonly Goal[]] | undefined => {
    if (!ordered(p.pairs, s, t)) return undefined;
    const paired = pairIds(sc, p.ids, s, t);
    if (paired === undefined) return undefined;
    const [expectedValue, actualValue] = compared(s.line, t.line);
    const walked = walkContent(sc.declared, t.at, s.at, expectedValue, actualValue, p.keys);
    if (walked === undefined) return undefined;
    return [{ ...p, ids: paired, keys: walked[0], pairs: [...p.pairs, { spec: s, trace: t }] }, walked[1]];
  };

  /** Returns the pairing with open snapshot subscription `id` paired with open implementation subscription `tid`. */
  const pairSubscription = (
    sc: Scope,
    p: Pairing,
    id: string,
    tid: string,
  ): readonly [Pairing, readonly Goal[]] | undefined => {
    const s = sc.openSnapshot.get(id);
    const t = sc.openTrace.get(tid);
    if (s === undefined || t === undefined || s.line.name !== t.line.name) return undefined;
    const walked = walkContent(sc.declared, t.at, s.at, contentOf(s.line), contentOf(t.line), p.keys);
    if (walked === undefined) return undefined;
    return [{ ...p, keys: walked[0], subscriptions: [...p.subscriptions, [id, tid]] }, walked[1]];
  };

  /** Returns the implementation `out` lines that are not paired yet and have the type, time and name of `s`. */
  const candidates = (sc: Scope, p: Pairing, s: NumberedLine): NumberedLine[] =>
    sc.traceOut.filter(
      (t) =>
        !p.pairs.some((q) => q.trace.at === t.at) &&
        t.line.type === s.line.type &&
        sameTime(s.line, t.line) &&
        (s.line.type === "answer" || nameOf(t.line) === nameOf(s.line)),
    );

  /**
   * Returns the ways to meet goal `g`, each with the goals left. Candidates with the same JSON give the same result in
   * the same pairing, so only the first of them is tried.
   */
  const expand = (sc: Scope, g: Goal, rest: readonly Goal[], p: Pairing): Frame[] => {
    const frames: Frame[] = [];
    const add = (found: readonly [Pairing, readonly Goal[]] | undefined, after: readonly Goal[] = []) => {
      if (found !== undefined) frames.push([[...found[1], ...after, ...rest], found[0]]);
    };
    if (g.kind === "out")
      for (const t of distinct(
        (t) => json([toOf(t.line) ?? null, compared(g.s.line, t.line)[1] ?? null]),
        candidates(sc, p, g.s),
      ))
        add(pairOut(sc, p, g.s, t));
    else if (g.kind === "subscription") {
      const name = sc.openSnapshot.get(g.id)?.line.name;
      const open = sc.openTrace
        .entries()
        .filter(([tid, t]) => !p.subscriptions.some(([, u]) => u === tid) && t.line.name === name);
      for (const [tid] of distinct(([, t]) => json(contentOf(t.line) ?? null), open))
        add(pairSubscription(sc, p, g.id, tid));
    } else {
      if (g.xs.length === 0) return [[rest, p]];
      const [x, ...more] = g.xs;
      for (const [i, y] of distinct(([, y]) => json(y), [...g.ys.entries()])) {
        const walked = walk(sc.declared, g.line, g.snapshotLine, x, y, p.keys);
        if (walked !== undefined)
          add([{ ...p, keys: walked[0] }, walked[1]], [{ ...g, xs: more, ys: g.ys.toSpliced(i, 1) }]);
      }
    }
    return frames;
  };

  /** Searches depth first over the frames of `stack`, each the goals left and the pairing so far. */
  const search = (sc: Scope, stack: Frame[]): Outcome => {
    let left = searchLimit;
    for (;;) {
      const frame = stack.pop();
      if (frame === undefined) return { kind: "unpaired" };
      const [[g, ...rest], p] = frame;
      if (g === undefined) return { kind: "paired", pairing: p };
      if (left === 0) return { kind: "limited" };
      left -= 1;
      stack.push(...expand(sc, g, rest, p).toReversed());
    }
  };

  /** Returns the pairing of all `goals`, unpaired at once when the counts differ or a goal has no candidate at the start. */
  const pairAll = (sc: Scope, goals: readonly Goal[], start: Pairing): Outcome =>
    goals.filter((g) => g.kind === "out").length !== sc.traceOut.length ||
    sc.openSnapshot.entries().length !== sc.openTrace.entries().length ||
    goals.some((g) => expand(sc, g, [], start).length === 0)
      ? { kind: "unpaired" }
      : search(sc, [[goals, start]]);

  const valueMismatch = (s: TraceLine, t: NumberedLine): Mismatch | undefined => {
    const at = t.at;
    const actualLine = t.line;
    const got = plain(contentOf(actualLine));
    const sub = (v: unknown) => plain(substitute(keys, v));
    if (s.type === "command" || s.type === "query")
      return {
        kind: "Mismatch.request",
        definition: null,
        data: { line: at, id: actualLine.id ?? null, type: s.type, name: s.name, snapshot: sub(s.input), trace: got },
      };
    if (s.type === "event")
      return {
        kind: "Mismatch.event",
        definition: null,
        data: { line: at, name: s.name, snapshot: sub(s.payload), trace: got },
      };
    if (s.type === "operation" || s.type === "unacceptedOperation")
      return {
        kind: "Mismatch.operation",
        definition: null,
        data: { line: at, name: s.name, snapshot: sub(s.payload), trace: got },
      };
    if (s.type !== "answer" || actualLine.type !== "answer") return undefined;
    const e = s.answer;
    const a = actualLine.answer;
    const to = actualLine.to;
    const output = (snapshot: unknown, trace: unknown): Mismatch => ({
      kind: "Mismatch.output",
      definition: null,
      data: { line: at, to, snapshot: sub(snapshot), trace: plain(trace) },
    });
    if (answersQuery(s.to)) return output(queryAnswer(s), queryAnswer(actualLine));
    if (e.result !== a.result)
      return { kind: "Mismatch.result", definition: null, data: { line: at, to, snapshot: e.result, trace: a.result } };
    if (e.result === "rejected" && a.result === "rejected")
      return {
        kind: "Mismatch.rejection",
        definition: null,
        data: { line: at, to, snapshot: e.rejection.kind, trace: a.rejection.kind },
      };
    if ((e.result === "accepted" && a.result === "accepted") || (e.result === "fulfilled" && a.result === "fulfilled"))
      return output(e.output, a.output);
    return undefined;
  };

  const missing = (s: NumberedLine, line: number): Mismatch =>
    s.line.type === "answer" || s.line.type === "unsubscribe"
      ? {
          kind: "Mismatch.missingAnswer",
          definition: null,
          data: { line, type: s.line.type, to: traceOf(ids.bound, s.line.to) ?? s.line.to, snapshotLine: s.at },
        }
      : {
          kind: "Mismatch.missingLine",
          definition: null,
          data: {
            line,
            type: s.line.type,
            name: nameOf(s.line) as string,
            content: plain(substitute(keys, contentOf(s.line))),
            snapshotLine: s.at,
          },
        };

  /** Returns the renaming under which the values are equal, bags included, or undefined. */
  const contentKeys = (
    sc: Scope,
    line: number,
    snapshotLine: number,
    s: unknown,
    t: unknown,
    p: Pairing,
  ): Renaming | undefined => {
    const walked = walkContent(sc.declared, line, snapshotLine, s, t, p.keys);
    if (walked === undefined) return undefined;
    const found = search(sc, [[walked[1], { ...p, keys: walked[0] }]]);
    return found.kind === "paired" ? found.pairing.keys : undefined;
  };

  /** Adds to each paired snapshot subscription the implementation subscriptions paired with alike subscriptions. */
  const subscribe = (sc: Scope, pairs: readonly (readonly [string, string])[]) => {
    const lineOf = (s: string) => sc.openSnapshot.get(s)?.line as TraceLine;
    for (const [s] of pairs) {
      const found = subscriptionIds.get(s) ?? new Set();
      for (const [other, t] of pairs) if (alike(lineOf(s), lineOf(other))) found.add(t);
      subscriptionIds.set(s, found);
    }
  };

  /**
   * Pairs the lines one by one, preferring equal lines, and reports the differences. When no line differs, including
   * the subscriptions reported in an earlier window, it reports the uses of each value that stands for two values.
   */
  const explain = (sc: Scope, specOut: readonly NumberedLine[], missingAt: number) => {
    const reported = problems.length;
    const keysBefore = keys.length;
    const pairs: { spec: NumberedLine; trace: NumberedLine }[] = [];
    const idUses: Use[] = [];
    const keyUses: Use[] = [];
    let repeated = false;
    for (const s of byRank(specOut)) {
      const p: Pairing = { ids, keys, pairs: [], subscriptions: [] };
      const cands = sc.traceOut.filter(
        (t) =>
          !pairs.some((q) => q.trace.at === t.at) &&
          t.line.type === s.line.type &&
          (s.line.type === "answer"
            ? useIds(ids, t.at, s.at, s.line.to, toOf(t.line)) !== undefined
            : nameOf(t.line) === nameOf(s.line)),
      );
      const keysOf = (t: NumberedLine) => {
        const [expectedValue, actualValue] = compared(s.line, t.line);
        return contentKeys(sc, t.at, s.at, expectedValue, actualValue, p);
      };
      const usesOf = (t: NumberedLine) => {
        const [expectedValue, actualValue] = compared(s.line, t.line);
        return freeContent(declared, t.at, s.at, expectedValue, actualValue);
      };
      const equal = (t: NumberedLine) => pairIds(sc, ids, s, t) !== undefined && keysOf(t) !== undefined;
      const t =
        cands.find((c) => equal(c) && sameTime(s.line, c.line)) ??
        cands.find(equal) ??
        cands.find((c) => usesOf(c) !== undefined) ??
        cands[0];
      if (t === undefined) {
        problems.push(missing(s, missingAt));
        continue;
      }
      pairs.push({ spec: s, trace: t });
      if (!sameTime(s.line, t.line))
        problems.push({
          kind: "Mismatch.time",
          definition: null,
          data: { line: t.at, subject: subjectOf(t.line), snapshot: s.line.time, trace: t.line.time },
        });
      const paired = pairIds(sc, ids, s, t);
      if (paired !== undefined) ids = paired;
      else if (s.line.id !== undefined && t.line.id !== undefined)
        idUses.push({ snapshot: s.line.id, trace: t.line.id, line: t.at, snapshotLine: s.at });
      const found = keysOf(t);
      const uses = usesOf(t);
      if (found !== undefined) keys = found;
      else if (uses !== undefined) keyUses.push(...uses);
      else {
        const m = valueMismatch(s.line, t);
        if (m !== undefined) problems.push(m);
      }
    }
    const subscriptions: (readonly [string, string])[] = [];
    for (const [id, s] of sc.openSnapshot.entries()) {
      const p: Pairing = { ids, keys, pairs: [], subscriptions: [] };
      const cands = sc.openTrace
        .entries()
        .filter(([tid, t]) => !subscriptions.some(([, u]) => u === tid) && t.line.name === s.line.name);
      const keysOf = (t: typeof s) => contentKeys(sc, t.at, s.at, contentOf(s.line), contentOf(t.line), p);
      const usesOf = (t: typeof s) => freeContent(declared, t.at, s.at, contentOf(s.line), contentOf(t.line));
      const chosen = cands.find(([, t]) => keysOf(t) !== undefined) ?? cands.find(([, t]) => usesOf(t) !== undefined);
      if (chosen !== undefined) {
        const [tid, t] = chosen;
        subscriptions.push([id, tid]);
        const found = keysOf(t);
        if (found !== undefined) keys = found;
        else keyUses.push(...(usesOf(t) ?? []));
      } else if (reportedMissing.has(id)) repeated = true;
      else {
        reportedMissing.add(id);
        problems.push({
          kind: "Mismatch.unopenedSubscription",
          definition: null,
          data: {
            line: missingAt,
            name: s.line.name,
            input: plain(substitute(keys, contentOf(s.line))),
            snapshotLine: s.at,
          },
        });
      }
    }
    for (const [tid, t] of sc.openTrace.entries())
      if (subscriptions.some(([, u]) => u === tid)) continue;
      else if (reportedUnexpected.has(tid)) repeated = true;
      else {
        reportedUnexpected.add(tid);
        problems.push({
          kind: "Mismatch.unexpectedSubscription",
          definition: null,
          data: { line: t.at, name: t.line.name, input: plain(contentOf(t.line)), id: tid },
        });
      }
    subscribe(sc, subscriptions);
    for (const { spec: s, trace: t } of pairs) {
      const before = pairs.find((p) => p.trace.at > t.at && follows.get(s.at)?.has(p.spec.at) === true);
      if (before !== undefined)
        problems.push({
          kind: "Mismatch.lineOrder",
          definition: null,
          data: { line: t.at, subject: subjectOf(t.line), before: subjectOf(before.trace.line) },
        });
    }
    for (const t of sc.traceOut)
      if (!pairs.some((p) => p.trace === t))
        problems.push({
          kind: "Mismatch.unexpectedLine",
          definition: null,
          data: { line: t.at, subject: subjectOf(t.line) },
        });
    if (repeated || problems.length > reported) return;
    const found = [...conflicts([...idUsesOf(ids), ...idUses]), ...conflicts([...keys, ...keyUses])];
    if (found.length === 0)
      problems.push({
        kind: "Mismatch.renaming",
        definition: null,
        data: { uses: [...keyUses, ...idUses, ...keys.slice(keysBefore)] },
      });
    else for (const uses of found) problems.push({ kind: "Mismatch.renaming", definition: null, data: { uses } });
  };

  const follow = (open: Open, lines: readonly NumberedLine[]) => {
    for (const o of lines)
      if (o.line.type === "subscribe" && o.line.id !== undefined) open.subscribe(o.line.id, { line: o.line, at: o.at });
      else if (o.line.type === "unsubscribe") open.unsubscribe(o.line.to);
  };
  const isSubscribing = (l: TraceLine) => l.type === "subscribe" || l.type === "unsubscribe";

  /**
   * Compares the `out` lines between two `in` lines, which follow the `in` lines `missingAt` and `snapshotAt`. Returns
   * the violation when the search stops at searchLimit.
   */
  const compareWindow = (
    allSpecOut: readonly NumberedLine[],
    allTraceOut: readonly NumberedLine[],
    missingAt: number,
    snapshotAt: number,
  ): Uncomparable | undefined => {
    for (const s of allSpecOut) for (const v of s.line.created ?? []) declared.add(v);
    window += 1;
    follow(
      openInSnapshot,
      allSpecOut.filter((s) => isSubscribing(s.line)),
    );
    follow(
      openInTrace,
      allTraceOut.filter((t) => isSubscribing(t.line)),
    );
    const specOut = allSpecOut.filter((s) => !isSubscribing(s.line) && !internal(s.line));
    const sc: Scope = {
      declared,
      window,
      traceOut: allTraceOut.filter((t) => !isSubscribing(t.line) && !internal(t.line)),
      openSnapshot: openInSnapshot,
      openTrace: openInTrace,
    };
    const goals: Goal[] = [
      ...byRank(specOut).map((s): Goal => ({ kind: "out", s })),
      ...openInSnapshot.entries().map(([id]): Goal => ({ kind: "subscription", id })),
    ];
    const found = pairAll(sc, goals, { ids, keys, pairs: [], subscriptions: [] });
    if (found.kind === "limited")
      return {
        kind: "Uncomparable.searchLimit",
        definition: null,
        data: { line: missingAt, snapshotLine: snapshotAt },
      };
    if (found.kind === "unpaired") explain(sc, specOut, missingAt);
    else {
      ids = found.pairing.ids;
      keys = found.pairing.keys;
      subscribe(sc, found.pairing.subscriptions);
    }
    return undefined;
  };

  /** Returns whether answer `t` answers the request that answer `s` answers, through a like subscription or the ids. */
  const answersPlaced = (current: Ids, s: NumberedLine, t: NumberedLine): Ids | undefined => {
    if (s.line.type !== "answer" || t.line.type !== "answer") return undefined;
    const subscribed = subscriptionIds.get(s.line.to);
    if (subscribed !== undefined) return subscribed.has(t.line.to) ? current : undefined;
    return useIds(current, t.at, s.at, s.line.to, t.line.to);
  };

  /** Returns the comparison of two `in` lines: the renamings under which they are the same. */
  const sameInput = (s: NumberedLine, t: NumberedLine): Outcome => {
    const [sl, tl] = [s.line, t.line];
    if (sl.type !== tl.type || nameOf(sl) !== nameOf(tl) || !sameTime(sl, tl)) return { kind: "unpaired" };
    const withId = useOwn(ids, t.at, s.at, sl.id, tl.id);
    if (withId === undefined) return { kind: "unpaired" };
    const placed =
      sl.type === "time" || sl.type === "restart"
        ? withId
        : sl.type === "unsubscribe"
          ? useIds(withId, t.at, s.at, sl.to, toOf(tl))
          : sl.type === "answer"
            ? answersPlaced(withId, s, t)
            : useIds(withId, t.at, s.at, resultOf(sl), resultOf(tl));
    if (placed === undefined) return { kind: "unpaired" };
    if (sl.type === "time" || sl.type === "restart" || sl.type === "unsubscribe")
      return { kind: "paired", pairing: { ids: placed, keys, pairs: [], subscriptions: [] } };
    const walked = walkContent(declared, t.at, s.at, contentOf(sl), contentOf(tl), keys);
    if (walked === undefined) return { kind: "unpaired" };
    const sc: Scope = {
      declared,
      window,
      traceOut: [],
      openSnapshot: new Subscriptions(),
      openTrace: new Subscriptions(),
    };
    return search(sc, [[walked[1], { ids: placed, keys: walked[0], pairs: [], subscriptions: [] }]]);
  };

  const count = malformed === undefined ? Math.max(expected.length, actual.length) : actual.length - 1;
  for (let k = 0; k < count; k += 1) {
    const previous = actual[k - 1]?.input;
    const previousSnapshot = expected[k - 1]?.input;
    const limited = compareWindow(
      expected[k]?.before ?? [],
      actual[k]?.before ?? [],
      previous === undefined ? 1 : previous.at,
      previousSnapshot === undefined ? 1 : previousSnapshot.at,
    );
    if (limited !== undefined) {
      problems.push(limited);
      return { found: problems, bindings: bindings() };
    }
    const s = expected[k]?.input;
    const t = actual[k]?.input;
    if (s === undefined && t === undefined) return { found: problems, bindings: bindings() };
    if (s === undefined) {
      const { at, line } = t as NumberedLine;
      problems.push({ kind: "Uncomparable.unexpectedInput", definition: null, data: { line: at, input: plain(line) } });
      return { found: problems, bindings: bindings() };
    }
    if (t === undefined) {
      problems.push({
        kind: "Uncomparable.missingInput",
        definition: null,
        data: { line: lines.length, input: plain(s.line), snapshotLine: s.at },
      });
      return { found: problems, bindings: bindings() };
    }
    const same = sameInput(s, t);
    if (same.kind === "limited") {
      problems.push({ kind: "Uncomparable.searchLimit", definition: null, data: { line: t.at, snapshotLine: s.at } });
      return { found: problems, bindings: bindings() };
    }
    if (same.kind === "unpaired") {
      problems.push(
        s.line.type === "answer" && t.line.type === "answer" && answersPlaced(ids, s, t) === undefined
          ? {
              kind: "Uncomparable.answersNoRequest",
              definition: null,
              data: { line: t.at, to: t.line.to, snapshotLine: s.at },
            }
          : {
              kind: "Uncomparable.differentInput",
              definition: null,
              data: { line: t.at, snapshotLine: s.at, snapshot: plain(substitute(keys, s.line)), trace: plain(t.line) },
            },
      );
      return { found: problems, bindings: bindings() };
    }
    ids = same.pairing.ids;
    keys = same.pairing.keys;
  }
  return { found: malformed === undefined ? problems : [...problems, lineSchema(malformed)], bindings: bindings() };
}
