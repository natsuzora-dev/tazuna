import { z } from "zod";
import { BagValue, bagValues, compareKeys, type Marked, runsOf, type SortKey } from "./bag.ts";
import { fieldSchema, namedOption, type SchemaNode, schemaNode } from "./schemaNode.ts";
import {
  byCodePoint,
  canonicalJson,
  type Fields,
  type Json,
  objectOf,
  plain,
  type Shape,
  strictObjectOf,
} from "./values.ts";

export type Collection =
  | { readonly kind: "bag" }
  | { readonly kind: "set" }
  | { readonly kind: "sortedBy"; readonly key: string };

/**
 * The collection of each marked array, keyed by a check rather than by the schema, because Zod copies checks into the
 * schemas that `.min()` and similar methods return.
 */
const collections = new WeakMap<object, Collection>();

/** An array schema whose output type carries mark `M`, so that spec functions may produce it from a Bag. */
type CollectionSchema<E extends z.ZodType, M extends "bag" | "sortedBy"> = z.ZodArray<E> & {
  readonly _zod: { readonly output: Marked<z.output<E>[], M> };
};

function marked<E extends z.ZodType, M extends "bag" | "sortedBy">(
  element: E,
  check: z.core.$ZodCheck<never>,
  collection: Collection,
): CollectionSchema<E, M> {
  collections.set(check, collection);
  return z.array(element).check(check as z.core.$ZodCheck<z.output<E>[]>) as CollectionSchema<E, M>;
}

const bagCheck = z.check<readonly unknown[]>(() => {});

const setCheck = z.check<readonly unknown[]>((ctx) => {
  const seen = new Set<string>();
  for (const [i, v] of ctx.value.entries()) {
    const text = canonicalJson(v);
    if (seen.has(text))
      ctx.issues.push({ code: "custom", message: `duplicate element ${text}`, input: ctx.value, path: [i] });
    seen.add(text);
  }
});

/** Returns an array schema whose element order means nothing, like OCL's Bag; `z.array` stays a sequence. */
export const bag = <E extends z.ZodType>(element: E): CollectionSchema<E, "bag"> =>
  marked(element, bagCheck as never, { kind: "bag" });

/**
 * Returns an array schema whose element order means nothing and whose two equal elements are an error, like OCL's Set.
 */
export const set = <E extends z.ZodType>(element: E): CollectionSchema<E, "bag"> =>
  marked(element, setCheck as never, { kind: "set" });

type SortKeyOf<E extends z.ZodObject> = {
  [K in keyof z.output<E>]-?: z.output<E>[K] extends SortKey ? K : never;
}[keyof z.output<E>] &
  string;

const byKey = (key: string) => (a: unknown, b: unknown) =>
  compareKeys((a as Record<string, unknown>)[key], (b as Record<string, unknown>)[key]);

/**
 * Returns an array schema sorted ascending by `key`, like Kotlin's `sortedBy`. tazuna sorts the values that the spec
 * produces, so `resolve` and `decide` do not sort; reading a value out of key order is an error.
 */
export function sortedBy<E extends z.ZodObject, K extends SortKeyOf<E>>(
  element: E,
  key: K,
): CollectionSchema<E, "sortedBy"> {
  const check = z.check<readonly Record<string, unknown>[]>((ctx) => {
    const i = ctx.value.findIndex((row, i) => i > 0 && byKey(key)(ctx.value[i - 1], row) > 0);
    if (i > 0)
      ctx.issues.push({
        code: "custom",
        message: `element ${i} is before element ${i - 1} in ${key} order`,
        input: ctx.value,
        path: [i],
      });
  });
  return marked(element, check as never, { kind: "sortedBy", key });
}

export const collectionOf = (schema: z.core.$ZodType): Collection | undefined =>
  (schema._zod.def.checks ?? []).map((c) => collections.get(c)).find((c) => c !== undefined);

/** Returns the elements of a marked array that spec code made from Bags, or the value itself if it is no such array. */
function unbagged(collection: Collection | undefined, value: unknown): unknown {
  if (collection === undefined) return value;
  const values = bagValues(value);
  if (values !== undefined) return values;
  return collection.kind === "sortedBy" && Array.isArray(value) ? value.flatMap((v) => bagValues(v) ?? [v]) : value;
}

/**
 * Returns the value with the elements of each bag and set in canonical JSON order, and each sortedBy array in key order
 * with equal keys in canonical JSON order, so that the order in which spec code built them leaves no trace. A Bag in a
 * bag or set, and a Bag or a run of Bags in a sortedBy array, become arrays.
 */
export function sorted(schema: z.ZodType, value: unknown): unknown {
  const node = schemaNode(schema);
  switch (node.type) {
    case "array": {
      const collection = collectionOf(schema);
      const array = unbagged(collection, value);
      if (!Array.isArray(array)) return array;
      const items = array.map((v) => sorted(node.element, v));
      if (collection === undefined) return items;
      const canonical = items.toSorted((a, b) => byCodePoint(canonicalJson(a), canonicalJson(b)));
      return collection.kind === "sortedBy" ? canonical.toSorted(byKey(collection.key)) : canonical;
    }
    case "object":
      if (!value || typeof value !== "object" || Array.isArray(value)) return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => {
          const field = fieldSchema(node, k);
          return [k, field === undefined ? v : sorted(field, v)];
        }),
      );
    case "union":
      return (unionOption(node, value, (o) => sorted(o, value)) ?? { value }).value;
    case "optional":
    case "nullable":
    case "default":
      return value == null ? value : sorted(node.inner, value);
    default:
      return value;
  }
}

/** Whether `sorted` and `bagged` walk into the node; a collection under any other node is opaque. */
export const sortsInside = (node: SchemaNode): boolean =>
  ["array", "object", "union", "optional", "nullable", "default"].includes(node.type);

/**
 * Returns the option of a union that `value` takes, with the value as `candidate` makes it for the option: the option
 * that its discriminator names, or in a plain union the first option that it passes, as in Zod.
 */
function unionOption(
  node: Extract<SchemaNode, { type: "union" }>,
  value: unknown,
  candidate: (option: z.ZodType) => unknown = () => value,
): { readonly option: z.ZodType; readonly value: unknown } | undefined {
  if (node.discriminator !== undefined) {
    const option = namedOption(node, value);
    return option && { option, value: candidate(option) };
  }
  return node.options
    .map((option) => ({ option, value: candidate(option) }))
    .find((t) => z.safeEncode(t.option, t.value as never).success);
}

/**
 * Returns a value that spec code made for `schema` as its sender writes it to a message, with each collection as
 * `sorted` orders it and encoded by toJson, so that only the receiver parses the value.
 */
export const written = (schema: z.ZodType, value: unknown): Json => plain(toJson(schema, sorted(schema, value)));

/**
 * Returns a value of `schema` as JSON holds it: each codec at any depth encodes its part, and no check or other
 * transform runs. A part that its codec cannot encode stays as it is. Check reports a plain union that holds a codec, so
 * a union picks the option that the discriminator names and needs no other choice.
 */
export function toJson(schema: z.ZodType, value: unknown): unknown {
  const node = schemaNode(schema);
  switch (node.type) {
    case "codec": {
      const wire = node.encode(toJson(node.out, value));
      return wire === undefined ? value : toJson(node.in, wire.value);
    }
    case "pipe":
      return toJson(node.in, toJson(node.out, value));
    case "array":
      return Array.isArray(value) ? value.map((v) => toJson(node.element, v)) : value;
    case "tuple":
      if (!Array.isArray(value)) return value;
      return value.map((v, i) => {
        const item = node.items[i] ?? node.rest;
        return item === undefined ? v : toJson(item, v);
      });
    case "object":
      if (!isRecord(value)) return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => {
          const field = fieldSchema(node, k);
          return [k, field === undefined ? v : toJson(field, v)];
        }),
      );
    case "record":
      if (!isRecord(value)) return value;
      return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, toJson(node.value, v)]));
    case "union": {
      const option = namedOption(node, value);
      return option === undefined ? value : toJson(option, value);
    }
    case "intersection":
      return toJson(node.right, toJson(node.left, value));
    case "lazy":
      return toJson(node.inner, value);
    case "opaque":
      return value == null || node.inner === undefined ? value : toJson(node.inner, value);
    default:
      return value == null ? value : toJson(node.inner, value);
  }
}

const isRecord = (value: unknown): value is Readonly<Record<string, unknown>> =>
  value !== null && typeof value === "object" && !Array.isArray(value);

/**
 * Returns a value as `sorted` returns it, as spec code receives it: each bag and set as a Bag, and each sortedBy array as
 * Runs.
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
      const key = (v: unknown) => (v as Record<string, SortKey>)[collection.key] as SortKey;
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
    case "union": {
      const chosen = unionOption(node, value);
      return chosen === undefined ? value : bagged(chosen.option, value);
    }
    case "optional":
    case "nullable":
    case "default":
      return value == null ? value : bagged(node.inner, value);
    default:
      return value;
  }
}

/** Returns the value with every collection sorted, or the reason that the value does not match the schema. */
function normalized<T>(schema: z.ZodType, value: T): { readonly value: T } | { readonly error: z.ZodError } {
  const sortedValue = sorted(schema, value) as T;
  const encoded = z.safeEncode(schema, sortedValue as never);
  return encoded.success ? { value: sortedValue } : { error: encoded.error };
}

export const normalizedRow = (
  shape: Shape,
  value: unknown,
): { readonly value: Fields } | { readonly error: z.ZodError } => normalized(strictObjectOf(shape), value as Fields);

/** Returns the row of the shape's defaults with every collection sorted; load checks it against the shape. */
export function defaultRow(shape: Shape): Fields {
  const object = objectOf(shape);
  return sorted(object, object.parse({})) as Fields;
}
