import { z } from "zod";
import { schemaNode } from "./schemaNode.ts";
import { byCodePoint, canonicalJson, type Fields, objectOf, type Shape, strictObjectOf } from "./values.ts";

export type Collection =
  | { readonly kind: "bag" }
  | { readonly kind: "set" }
  | { readonly kind: "sortedBy"; readonly key: string };

/**
 * The collection of each marked array, keyed by a check rather than by the schema, because Zod copies checks into the
 * schemas that `.min()` and similar methods return.
 */
const collections = new WeakMap<object, Collection>();

function marked<E extends z.ZodType>(
  element: E,
  check: z.core.$ZodCheck<never>,
  collection: Collection,
): z.ZodArray<E> {
  collections.set(check, collection);
  return z.array(element).check(check as z.core.$ZodCheck<z.output<E>[]>);
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
export const bag = <E extends z.ZodType>(element: E): z.ZodArray<E> =>
  marked(element, bagCheck as never, { kind: "bag" });

/**
 * Returns an array schema whose element order means nothing and whose two equal elements are an error, like OCL's Set.
 */
export const set = <E extends z.ZodType>(element: E): z.ZodArray<E> =>
  marked(element, setCheck as never, { kind: "set" });

/** A value that orders others: a number or a point in time, not a string, whose order differs across languages. */
export type SortKey = number | Temporal.Instant | Temporal.PlainDate;
type SortKeyOf<E extends z.ZodObject> = {
  [K in keyof z.output<E>]-?: z.output<E>[K] extends SortKey ? K : never;
}[keyof z.output<E>] &
  string;

export function compareKeys(a: unknown, b: unknown): number {
  if (a instanceof Temporal.Instant && b instanceof Temporal.Instant) return Temporal.Instant.compare(a, b);
  if (a instanceof Temporal.PlainDate && b instanceof Temporal.PlainDate) return Temporal.PlainDate.compare(a, b);
  return typeof a === "number" && typeof b === "number" ? a - b : 0;
}

const byKey = (key: string) => (a: unknown, b: unknown) =>
  compareKeys((a as Record<string, unknown>)[key], (b as Record<string, unknown>)[key]);

/**
 * Returns an array schema sorted ascending by `key`, like Kotlin's `sortedBy`. tazuna sorts the values that the spec
 * produces, so `resolve` and `decide` do not sort; reading a value out of key order is an error.
 */
export function sortedBy<E extends z.ZodObject, K extends SortKeyOf<E>>(element: E, key: K): z.ZodArray<E> {
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

/**
 * Returns the value with the elements of each bag and set in canonical JSON order, and each sortedBy array in key order
 * with equal keys in canonical JSON order, so that the order in which spec code built them leaves no trace.
 */
export function sorted(schema: z.ZodType, value: unknown): unknown {
  const node = schemaNode(schema);
  switch (node.type) {
    case "array": {
      if (!Array.isArray(value)) return value;
      const items = value.map((v) => sorted(node.element, v));
      const collection = collectionOf(schema);
      if (collection === undefined) return items;
      const canonical = items.toSorted((a, b) => byCodePoint(canonicalJson(a), canonicalJson(b)));
      return collection.kind === "sortedBy" ? canonical.toSorted(byKey(collection.key)) : canonical;
    }
    case "object":
      if (!value || typeof value !== "object" || Array.isArray(value)) return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => [k, node.shape[k] === undefined ? v : sorted(node.shape[k], v)]),
      );
    case "union":
      for (const option of node.options) {
        const candidate = sorted(option, value);
        if (z.safeEncode(option, candidate as never).success) return candidate;
      }
      return value;
    case "opaque":
      return value;
    default:
      return value == null ? value : sorted(node.inner, value);
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
