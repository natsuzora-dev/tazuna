import { Bag, Ref, Runs } from "./canonical.ts";

/** Lean's Bound: a value with its domain, written as one string, the domain first. */
export type Bound = string;

export const bound = (domain: string, value: string): Bound => `${domain}\u0000${value}`;

export const domainPart = (b: Bound): string => b.slice(0, b.indexOf("\u0000"));

export const valuePart = (b: Bound): string => b.slice(b.indexOf("\u0000") + 1);

/** Lean's Binding: snapshot values paired with implementation values, one to one, in the order they were bound. */
export interface Binding {
  readonly pairs: readonly (readonly [Bound, Bound])[];
  readonly forward: ReadonlyMap<Bound, Bound>;
  readonly images: ReadonlySet<Bound>;
}

export const emptyBinding: Binding = { pairs: [], forward: new Map(), images: new Set() };

/** Lean's Binding.same. */
export const sameBinding = (a: Binding, b: Binding): boolean =>
  a.pairs.length === b.pairs.length && a.pairs.every(([s, t]) => b.forward.get(s) === t);

/** Lean's Binding.image. */
export const imageOf = (b: Binding, s: Bound): string => {
  const t = b.forward.get(s);
  return t === undefined ? valuePart(s) : valuePart(t);
};

/** Lean's bindingLimit. */
export const bindingLimit = 256;

/** Lean's Binding.bindString. */
export function bindString(fresh: boolean, b: Binding, s: Bound, t: Bound): Binding | undefined {
  const bt = b.forward.get(s);
  if (bt !== undefined) return bt === t ? b : undefined;
  if (!fresh && s === t && domainPart(s) === "") return b;
  if (b.images.has(t)) return undefined;
  if (!(fresh || s === t)) return undefined;
  return { pairs: [...b.pairs, [s, t]], forward: new Map([...b.forward, [s, t]]), images: new Set([...b.images, t]) };
}

/** Lean's Binding.strings. */
export const stringPairs = (b: Binding): [string, string][] => b.pairs.map(([s, t]) => [valuePart(s), valuePart(t)]);

/** Lean's distinctBy. */
export function distinctBy<T>(same: (a: T, b: T) => boolean, xs: readonly T[]): T[] {
  const kept: T[] = [];
  for (const x of xs) if (!kept.some((k) => same(x, k))) kept.push(x);
  return kept;
}

/** Lean's limited: `undefined` when the states are more than bindingLimit. */
function limited<T>(same: (a: T, b: T) => boolean, states: readonly T[]): T[] | undefined {
  const kept = distinctBy(same, states);
  return kept.length > bindingLimit ? undefined : kept;
}

/** Lean's expand. */
export function expand<S, T>(
  same: (a: T, b: T) => boolean,
  states: readonly S[],
  next: (s: S) => readonly T[] | undefined,
): T[] | undefined {
  const all: T[] = [];
  for (const s of states) {
    const ns = next(s);
    if (ns === undefined) return undefined;
    all.push(...ns);
  }
  return limited(same, all);
}

/** Lean's Matches: the bindings under which two values compare equal, or `undefined` when over bindingLimit. */
export type Matches = readonly Binding[] | undefined;

/** Lean's Matches.andThen. */
export const andThen = (m: Matches, f: (b: Binding) => Matches): Matches =>
  m === undefined ? undefined : expand(sameBinding, m, f);

/** Lean's sameSet. */
export const sameSet = <T>(
  a: readonly T[],
  b: readonly T[],
  eq: (x: T, y: T) => boolean = (x, y) => x === y,
): boolean => a.length === b.length && a.every((x) => b.some((y) => eq(x, y)));

const isPlainObject = (v: unknown): v is Record<string, unknown> =>
  v !== null &&
  typeof v === "object" &&
  !Array.isArray(v) &&
  !(v instanceof Bag) &&
  !(v instanceof Runs) &&
  !(v instanceof Ref);

/** Lean's Values: the domain of each snapshot value (valueDomains), and the fresh values so far. */
export interface Values {
  readonly domain: (s: string) => string;
  readonly fresh: ReadonlySet<string>;
}

/** Lean's Values.bind. */
export const bind = (v: Values, b: Binding, s: string, t: string): Matches => {
  const c = bindString(v.fresh.has(s), b, bound(v.domain(s), s), bound(v.domain(s), t));
  return c === undefined ? [] : [c];
};

/** Lean's matchValue. */
export function matchValue(v: Values, b: Binding, s: unknown, t: unknown): Matches {
  if (typeof s === "string" && typeof t === "string") return bind(v, b, s, t);
  if (s instanceof Ref && t instanceof Ref) return bind(v, b, s.value, t.value);
  if (s instanceof Bag && t instanceof Bag)
    return s.items.length === t.items.length ? matchBag(v, b, s.items, t.items) : [];
  if (s instanceof Runs && t instanceof Runs) return matchList(v, b, s.runs, t.runs);
  if (Array.isArray(s) && Array.isArray(t)) return matchList(v, b, s, t);
  if (isPlainObject(s) && isPlainObject(t)) {
    const ks = Object.keys(s);
    const kt = Object.keys(t);
    if (ks.length !== kt.length || !ks.every((k) => kt.includes(k))) return [];
    const fields = (c: Binding, k: number): Matches => {
      const key = ks[k];
      return key === undefined ? [c] : andThen(matchValue(v, c, s[key], t[key]), (d) => fields(d, k + 1));
    };
    return fields(b, 0);
  }
  const leaf = (x: unknown) => x === null || typeof x !== "object";
  return leaf(s) && leaf(t) && typeof s !== "string" && typeof t !== "string" && s === t ? [b] : [];
}

/** Lean's matchList. */
function matchList(v: Values, b: Binding, xs: readonly unknown[], ys: readonly unknown[]): Matches {
  if (xs.length !== ys.length) return [];
  const from = (c: Binding, i: number): Matches =>
    i === xs.length ? [c] : andThen(matchValue(v, c, xs[i], ys[i]), (d) => from(d, i + 1));
  return from(b, 0);
}

/** Lean's matchBag. */
function matchBag(v: Values, b: Binding, xs: readonly unknown[], ys: readonly unknown[]): Matches {
  type Way = readonly [Binding, readonly number[]];
  const same = (p: Way, q: Way) => sameBinding(p[0], q[0]) && sameSet(p[1], q[1]);
  let ways: readonly Way[] | undefined = [[b, []]];
  for (const x of xs) {
    ways = expand(same, ways, ([c, used]) => {
      const next: Way[] = [];
      for (const [j, y] of ys.entries()) {
        if (used.includes(j)) continue;
        const ds = matchValue(v, c, x, y);
        if (ds === undefined) return undefined;
        for (const d of ds) next.push([d, [...used, j]]);
      }
      return next;
    });
    if (ways === undefined) return undefined;
  }
  return limited(
    sameBinding,
    ways.map(([c]) => c),
  );
}
