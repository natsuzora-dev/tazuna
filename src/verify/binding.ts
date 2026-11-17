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
export function limited<T>(same: (a: T, b: T) => boolean, states: readonly T[]): T[] | undefined {
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
