import type { DateLabel } from "./time.ts";
/** A value that orders others: a number or a date label, whose text orders as its day does. */
export type SortKey = number | DateLabel;

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
