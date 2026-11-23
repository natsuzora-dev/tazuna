import type { z } from "zod";
import type { Bag, Runs, SortKey } from "../../src/data/bag.ts";
import { collectionOf } from "../../src/data/marks.ts";
import { fieldSchema, schemaNode } from "../../src/data/schemaNode.ts";

// The TS evaluation of spec functions that the converter diff tests compare with Lean's. No command runs it.

/** Compares two keys. NaN throws, as it is neither less than, equal to nor greater than another number. */
function compareKeys(a: unknown, b: unknown): number {
  if (Number.isNaN(a) || Number.isNaN(b)) throw new RangeError("NaN is not a sort key");
  if (typeof a === "string" && typeof b === "string") return a < b ? -1 : a > b ? 1 : 0;
  return typeof a === "number" && typeof b === "number" ? a - b : 0;
}

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

/**
 * Returns a decoded value of `schema` as spec code receives it: each bag and set as a Bag, and each sortedBy array as
 * Runs. The fixtures' schemas hold no codec and no union, so their JSON is already the decoded value.
 */
export function bagged(schema: z.ZodType, value: unknown): unknown {
  const node = schemaNode(schema);
  switch (node.type) {
    case "array": {
      if (!Array.isArray(value)) return value;
      const items = value.map((v) => bagged(node.element, v));
      const collection = collectionOf(schema);
      if (collection === undefined) return items;
      if (collection.kind !== "sortedBy") return new BagValue(() => items);
      const key = (row: unknown) => (row as Readonly<Record<string, SortKey>>)[collection.key] as SortKey;
      return runsOf(items, key).map((run) => new BagValue(() => run));
    }
    case "object":
      if (!value || typeof value !== "object" || Array.isArray(value)) return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => {
          const field = fieldSchema(node, k);
          return [k, field === undefined ? v : bagged(field, v)];
        }),
      );
    case "optional":
    case "nullable":
    case "default":
      return value == null ? value : bagged(node.inner, value);
    default:
      return value;
  }
}
