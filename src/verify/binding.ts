/** Lean's Bound: a value with its domain, written as one string, the domain first. */
export type Bound = string;

export const bound = (domain: string, value: string): Bound => `${domain}\u0000${value}`;

const domainPart = (b: Bound): string => b.slice(0, b.indexOf("\u0000"));

export const valuePart = (b: Bound): string => b.slice(b.indexOf("\u0000") + 1);

/** Lean's Slot: snapshot values and the implementation values that they stand for, in some order. */
export type Slot = readonly [readonly Bound[], readonly Bound[]];

/** Lean's Binding: no value is in two slots, on either side, and each slot holds as many values on each side. */
export interface Binding {
  readonly slots: readonly Slot[];
}

export const emptyBinding: Binding = { slots: [] };

const domainOf = (slots: readonly Slot[]): string[] => slots.flatMap(([s]) => s);

const imageOf = (slots: readonly Slot[]): string[] => slots.flatMap(([, t]) => t);

/** Lean's resolveIn. */
function resolveIn(s: Bound, t: Bound, slots: readonly Slot[]): Slot[] | undefined {
  const k = slots.findIndex(([ss]) => ss.includes(s));
  const slot = slots[k];
  if (slot === undefined || !slot[1].includes(t)) return undefined;
  if (slot[0].length === 1) return [...slots];
  const without = (xs: readonly string[], x: string) => xs.toSpliced(xs.indexOf(x), 1);
  return [...slots.slice(0, k), [[s], [t]], [without(slot[0], s), without(slot[1], t)], ...slots.slice(k + 1)];
}

/** Lean's Binding.bindString. */
export function bindString(fresh: boolean, b: Binding, s: Bound, t: Bound): Binding | undefined {
  if (domainOf(b.slots).includes(s)) {
    const slots = resolveIn(s, t, b.slots);
    return slots === undefined ? undefined : { slots };
  }
  if (!fresh && s === t && domainPart(s) === "") return b;
  if (imageOf(b.slots).includes(t)) return undefined;
  return fresh || s === t ? { slots: [...b.slots, [[s], [t]]] } : undefined;
}

const distinct = (xs: readonly string[]) => new Set(xs).size === xs.length;

/** Lean's Valid. */
const valid = (slots: readonly Slot[]): boolean =>
  distinct(domainOf(slots)) && distinct(imageOf(slots)) && slots.every(([s, t]) => s.length === t.length);

/** Lean's Refines. */
const refines = (a: readonly Slot[], b: readonly Slot[]): boolean =>
  a.every(([ss, ts]) =>
    ss.every((s) =>
      b.some(([s2, t2]) => s2.includes(s) && s2.every((x) => ss.includes(x)) && t2.every((y) => ts.includes(y))),
    ),
  );

/** Lean's Binding.refine. */
export const refine = (b: Binding, slots: readonly Slot[]): Binding | undefined =>
  valid(slots) && refines(b.slots, slots) ? { slots } : undefined;

/** Lean's Binding.pairs. */
const pairsOf = (b: Binding): [Bound, Bound][] =>
  b.slots.flatMap(([ss, ts]) => ss.flatMap((s, i): [Bound, Bound][] => (i < ts.length ? [[s, ts[i] as Bound]] : [])));

/** Lean's Binding.strings. */
export const stringPairs = (b: Binding): [string, string][] => pairsOf(b).map(([s, t]) => [valuePart(s), valuePart(t)]);

/** Lean's bindSlots. */
export function bindSlots(slots: readonly Slot[], s: Bound, t: Bound): readonly Slot[] | undefined {
  if (domainOf(slots).includes(s)) return resolveIn(s, t, slots);
  return imageOf(slots).includes(t) ? undefined : [...slots, [[s], [t]]];
}

/** Lean's refineSlots. */
export function refineSlots(
  slots: readonly Slot[],
  σs: readonly string[],
  τs: readonly string[],
): readonly Slot[] | undefined {
  if (!distinct(σs) || !distinct(τs)) return undefined;
  const domain = domainOf(slots);
  const image = imageOf(slots);
  if (σs.every((s) => !domain.includes(s)) && τs.every((t) => !image.includes(t))) return [...slots, [σs, τs]];
  const k = slots.find(([ss, ts]) => σs.every((s) => ss.includes(s)) && τs.every((t) => ts.includes(t)));
  if (k === undefined) return undefined;
  const rest: Slot = [k[0].filter((s) => !σs.includes(s)), k[1].filter((t) => !τs.includes(t))];
  return slots.flatMap((k2): Slot[] => (sameSlot(k2, k) ? [[σs, τs], ...(rest[0].length === 0 ? [] : [rest])] : [k2]));
}

export const sameSlot = (a: Slot, b: Slot): boolean =>
  a[0].length === b[0].length &&
  a[1].length === b[1].length &&
  a[0].every((x, i) => x === b[0][i]) &&
  a[1].every((x, i) => x === b[1][i]);

/** Lean's singletons. */
export const singletons = (slots: readonly Slot[]): (readonly [string, string])[] =>
  slots.flatMap(([ss, ts]) => {
    const [s] = ss;
    const [t] = ts;
    return ss.length === 1 && ts.length === 1 && s !== undefined && t !== undefined ? [[s, t] as const] : [];
  });
