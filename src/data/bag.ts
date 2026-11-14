/** A value that orders others: a number or a point in time, not a string, whose order differs across languages. */
export type SortKey = number | Temporal.Instant | Temporal.PlainDate;

export function compareKeys(a: unknown, b: unknown): number {
  if (a instanceof Temporal.Instant && b instanceof Temporal.Instant) return Temporal.Instant.compare(a, b);
  if (a instanceof Temporal.PlainDate && b instanceof Temporal.PlainDate) return Temporal.PlainDate.compare(a, b);
  return typeof a === "number" && typeof b === "number" ? a - b : 0;
}

declare const collectionMark: unique symbol;
/** An array type that a bag, set or sortedBy schema outputs, and Runs; implementations still see a plain array. */
export type Marked<T, M extends "bag" | "sortedBy"> = T & { readonly [collectionMark]?: M };

/** The mark of an array type that a bag, set or sortedBy schema outputs, or never for another type. */
export type MarkOf<T> = typeof collectionMark extends keyof T ? NonNullable<T[typeof collectionMark]> : never;

type Leaf = Temporal.Instant | Temporal.PlainDate | Temporal.Duration;

/**
 * A value as spec functions may produce one that they receive as `T`: a Bag also takes an array, and Runs also take a
 * Bag or an array of values and Bags.
 */
export type Made<T> = T extends Leaf
  ? T
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
export const valuesOf = (value: unknown): readonly unknown[] | undefined =>
  value instanceof BagValue ? itemsOf(value) : undefined;

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
  /** The sum of `f` over the values; a value or sum that is not a safe integer throws. */
  sum(f: (value: T) => number): number;
  /** The least key, or undefined for no values. */
  min<K extends SortKey>(f: (value: T) => K): K | undefined;
  /** The greatest key, or undefined for no values. */
  max<K extends SortKey>(f: (value: T) => K): K | undefined;
  /** The one value, or undefined for no values; more than one value is Fault.notOnly. */
  only(): T | undefined;
  /** The values in groups of equal key, in ascending key order. */
  sortedBy(f: (value: T) => SortKey): Runs<T>;
  concat(other: Bag<T>): Bag<T>;
}

/** Groups of values in ascending key order; the values of one group have equal keys and no order. */
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
    itemsOf = (bag) => bag.#items();
  }

  static #of<T>(items: readonly T[]): Bag<T> {
    return new BagValue(() => items);
  }

  static #itemsOf<T>(values: Bag<T> | readonly T[]): readonly T[] {
    if (values instanceof BagValue) return values.#items();
    if (Array.isArray(values)) return values;
    throw new TypeError("not a Bag or an array");
  }

  get size(): number {
    return this.#items().length;
  }

  filter<S extends T>(predicate: (value: T) => value is S): Bag<S>;
  filter(predicate: (value: T) => boolean): Bag<T>;
  filter(predicate: (value: T) => boolean): Bag<T> {
    return BagValue.#of(this.#items().filter((v) => predicate(v)));
  }

  map<U>(f: (value: T) => U): Bag<U> {
    return BagValue.#of(this.#items().map((v) => f(v)));
  }

  flatMap<U>(f: (value: T) => Bag<U> | readonly U[]): Bag<U> {
    return BagValue.#of(this.#items().flatMap((v) => BagValue.#itemsOf(f(v))));
  }

  // Every value is visited, so a closure that the predicate mutates cannot tell where the search stopped.
  some(predicate: (value: T) => boolean): boolean {
    return this.#items()
      .map((v) => predicate(v))
      .includes(true);
  }

  every<S extends T>(predicate: (value: T) => value is S): this is Bag<S>;
  every(predicate: (value: T) => boolean): boolean;
  every(predicate: (value: T) => boolean): boolean {
    return !this.#items()
      .map((v) => predicate(v))
      .includes(false);
  }

  sum(f: (value: T) => number): number {
    return this.#items().reduce((total, v) => {
      const n = f(v);
      if (!Number.isSafeInteger(n)) throw new RangeError(`sum of ${n}, which is not a safe integer`);
      const next = total + n;
      if (!Number.isSafeInteger(next)) throw new RangeError(`sum ${next} is not a safe integer`);
      return next;
    }, 0);
  }

  min<K extends SortKey>(f: (value: T) => K): K | undefined {
    return this.#items()
      .map((v) => f(v))
      .reduce<K | undefined>((m, k) => (m === undefined || compareKeys(k, m) < 0 ? k : m), undefined);
  }

  max<K extends SortKey>(f: (value: T) => K): K | undefined {
    return this.#items()
      .map((v) => f(v))
      .reduce<K | undefined>((m, k) => (m === undefined || compareKeys(k, m) > 0 ? k : m), undefined);
  }

  only(): T | undefined {
    const items = this.#items();
    if (items.length > 1) throw new NotOnly(`only() on ${items.length} values`);
    return items[0];
  }

  sortedBy(f: (value: T) => SortKey): Runs<T> {
    const keyed = this.#items()
      .map((value) => ({ value, key: f(value) }))
      .toSorted((a, b) => compareKeys(a.key, b.key));
    const runs: T[][] = [];
    keyed.forEach(({ value, key }, i) => {
      if (i > 0 && compareKeys(keyed[i - 1]?.key, key) === 0) runs.at(-1)?.push(value);
      else runs.push([value]);
    });
    return runs.map((r) => BagValue.#of(r));
  }

  concat(other: Bag<T>): Bag<T> {
    return BagValue.#of([...this.#items(), ...BagValue.#itemsOf(other)]);
  }
}
