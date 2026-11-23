import type { DateLabel } from "./time.ts";
/** A value that orders others: a number or a date label, whose text orders as its day does. */
export type SortKey = number | DateLabel;

/** Compares two keys. NaN throws, as it is neither less than, equal to nor greater than another number. */
function compareKeys(a: unknown, b: unknown): number {
  if (Number.isNaN(a) || Number.isNaN(b)) throw new RangeError("NaN is not a sort key");
  if (typeof a === "string" && typeof b === "string") return a < b ? -1 : a > b ? 1 : 0;
  return typeof a === "number" && typeof b === "number" ? a - b : 0;
}

declare const collectionMark: unique symbol;
/** An array type that a bag, set or sortedBy schema outputs, and Runs. Implementations still see a plain array. */
export type Marked<T, M extends "bag" | "sortedBy"> = T & { readonly [collectionMark]?: M };

/** The mark of an array type that a bag, set or sortedBy schema outputs, or never for another type. */
export type MarkOf<T> = typeof collectionMark extends keyof T ? NonNullable<T[typeof collectionMark]> : never;

/**
 * A value as spec functions may produce one that they receive as `T`: a date also takes a string, which its schema
 * checks, a Bag also takes an array, and Runs also take a Bag or an array of values and Bags.
 */
export type Made<T> = T extends DateLabel
  ? T | string
  : T extends Bag<infer E>
    ? Bag<Made<E>> | readonly Made<E>[]
    : T extends readonly (infer E)[]
      ? [MarkOf<T>] extends [never]
        ? readonly Made<E>[]
        : E extends Bag<infer V>
          ? Bag<Made<V>> | readonly (Made<V> | Bag<Made<V>>)[]
          : never
      : T extends object
        ? { readonly [K in keyof T]: Made<T[K]> }
        : T;

let itemsOf: (bag: BagValue<unknown>) => readonly unknown[];

/** The values of a Bag, or undefined for any other value. */
export const bagValues = (value: unknown): readonly unknown[] | undefined =>
  value instanceof BagValue ? itemsOf(value) : undefined;

/** Groups `items` by equal keys of `f`, in ascending key order, each group in the order of `items`. */
export function runsOf<T>(items: readonly T[], f: (value: T) => SortKey): T[][] {
  const keyed = items.map((value) => ({ value, key: f(value) })).toSorted((a, b) => compareKeys(a.key, b.key));
  const runs: T[][] = [];
  keyed.forEach(({ value, key }, i) => {
    if (i > 0 && compareKeys(keyed[i - 1]?.key, key) === 0) runs.at(-1)?.push(value);
    else runs.push([value]);
  });
  return runs;
}

/**
 * Values without order, like OCL's Bag, as spec functions receive records. It has no index and no iterator, and each
 * callback receives only the value, so no result depends on an order.
 */
export interface Bag<T> {
  readonly size: number;
  filter<S extends T>(predicate: (value: T) => value is S): Bag<S>;
  filter(predicate: (value: T) => boolean): Bag<T>;
  map<U>(f: (value: T) => U): Bag<U>;
  flatMap<U>(f: (value: T) => Bag<U> | readonly U[]): Bag<U>;
  some(predicate: (value: T) => boolean): boolean;
  every<S extends T>(predicate: (value: T) => value is S): this is Bag<S>;
  every(predicate: (value: T) => boolean): boolean;
  /** The sum of `f` over the values. A value or sum that is not a safe integer throws. */
  sum(f: (value: T) => number): number;
  /** The least key, or undefined for no values. */
  min<K extends SortKey>(f: (value: T) => K): K | undefined;
  /** The greatest key, or undefined for no values. */
  max<K extends SortKey>(f: (value: T) => K): K | undefined;
  /** The value of the least key, or undefined for no values. More than one value of that key is `Fault.notOnly`. */
  minBy(f: (value: T) => SortKey): T | undefined;
  /** The value of the greatest key, or undefined for no values. More than one value of that key is `Fault.notOnly`. */
  maxBy(f: (value: T) => SortKey): T | undefined;
  /** The one value, or undefined for no values. More than one value is `Fault.notOnly`. */
  only(): T | undefined;
  /** The values in groups of equal key, in ascending key order. */
  sortedBy(f: (value: T) => SortKey): Runs<T>;
  concat(other: Bag<T>): Bag<T>;
}

/** Groups of values in ascending key order. The values of one group have equal keys and no order. */
export type Runs<T> = Marked<readonly Bag<T>[], "sortedBy">;

/** The error of `only()` on more than one value. */
export class NotOnly extends Error {}

/** A Bag whose values come from `items` on each read, so that a records view hears every read of its keys. */
export class BagValue<T> implements Bag<T> {
  readonly #items: () => readonly T[];

  constructor(items: () => readonly T[]) {
    this.#items = items;
  }

  static {
    itemsOf = (bag) => bag.#values();
  }

  static #of<T>(items: readonly T[]): Bag<T> {
    return new BagValue(() => items);
  }

  static #itemsOf<T>(values: Bag<T> | readonly T[]): readonly T[] {
    if (values instanceof BagValue) return values.#values();
    if (Array.isArray(values)) return values;
    throw new TypeError("not a Bag or an array");
  }

  #values(): readonly T[] {
    return this.#items();
  }

  get size(): number {
    return this.#items().length;
  }

  filter<S extends T>(predicate: (value: T) => value is S): Bag<S>;
  filter(predicate: (value: T) => boolean): Bag<T>;
  filter(predicate: (value: T) => boolean): Bag<T> {
    return BagValue.#of(this.#values().filter((v) => predicate(v)));
  }

  map<U>(f: (value: T) => U): Bag<U> {
    return BagValue.#of(this.#values().map((v) => f(v)));
  }

  flatMap<U>(f: (value: T) => Bag<U> | readonly U[]): Bag<U> {
    return BagValue.#of(this.#values().flatMap((v) => BagValue.#itemsOf(f(v))));
  }

  // Every value is visited, so a closure that the predicate mutates cannot tell where the search stopped.
  some(predicate: (value: T) => boolean): boolean {
    return this.#values()
      .map((v) => predicate(v))
      .includes(true);
  }

  every<S extends T>(predicate: (value: T) => value is S): this is Bag<S>;
  every(predicate: (value: T) => boolean): boolean;
  every(predicate: (value: T) => boolean): boolean {
    return !this.#values()
      .map((v) => predicate(v))
      .includes(false);
  }

  // Neither which value fails nor whether a partial sum overflows may depend on the order, so only the whole sum counts.
  sum(f: (value: T) => number): number {
    const ns = this.#values().map((v) => f(v));
    if (!ns.every((n) => Number.isSafeInteger(n))) throw new RangeError("sum of a value that is not a safe integer");
    const total = Number(ns.reduce((t, n) => t + BigInt(n), 0n));
    if (!Number.isSafeInteger(total)) throw new RangeError(`sum ${total} is not a safe integer`);
    return total;
  }

  min<K extends SortKey>(f: (value: T) => K): K | undefined {
    return this.#values()
      .map((v) => f(v))
      .reduce<K | undefined>((m, k) => (m === undefined || compareKeys(k, m) < 0 ? k : m), undefined);
  }

  max<K extends SortKey>(f: (value: T) => K): K | undefined {
    return this.#values()
      .map((v) => f(v))
      .reduce<K | undefined>((m, k) => (m === undefined || compareKeys(k, m) > 0 ? k : m), undefined);
  }

  minBy(f: (value: T) => SortKey): T | undefined {
    const least = this.min(f);
    return this.filter((v) => f(v) === least).only();
  }

  maxBy(f: (value: T) => SortKey): T | undefined {
    const greatest = this.max(f);
    return this.filter((v) => f(v) === greatest).only();
  }

  only(): T | undefined {
    const items = this.#values();
    if (items.length > 1) throw new NotOnly(`only() on ${items.length} values`);
    return items[0];
  }

  sortedBy(f: (value: T) => SortKey): Runs<T> {
    return runsOf(this.#values(), f).map((r) => BagValue.#of(r));
  }

  concat(other: Bag<T>): Bag<T> {
    return BagValue.#of([...this.#values(), ...BagValue.#itemsOf(other)]);
  }
}
