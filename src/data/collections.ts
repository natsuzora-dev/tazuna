import { z } from "zod";
import { BagValue, bagValues, compareKeys, type Marked, runsOf, type SortKey } from "./bag.ts";
import { InternalError } from "./internalError.ts";
import { type JsonSchema, jsonSchema } from "./jsonSchema.ts";
import { type Collection, collectionOf, mark } from "./marks.ts";
import { fieldSchema, type SchemaNode, schemaNode } from "./schemaNode.ts";
import { type DateLabel, date } from "./time.ts";
import { field, fits, unionOptions } from "./unionOptions.ts";
import { byCodePoint, canonicalJson, type Fields, type Json, plain, type Shape } from "./values.ts";

/** An array schema whose output type carries mark `M`, so that spec functions may produce it from a Bag. */
type CollectionSchema<E extends z.ZodType, M extends "bag" | "sortedBy"> = z.ZodArray<E> & {
  readonly _zod: { readonly output: Marked<z.output<E>[], M> };
};

function marked<E extends z.ZodType, M extends "bag" | "sortedBy">(
  element: E,
  check: z.core.$ZodCheck<never>,
  collection: Collection,
): CollectionSchema<E, M> {
  mark(check, collection);
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

/** Returns an array schema whose element order means nothing, like OCL's Bag. `z.array` stays a sequence. */
export const bag = <E extends z.ZodType>(element: E): CollectionSchema<E, "bag"> =>
  marked(element, bagCheck as never, { kind: "bag" });

/**
 * Returns an array schema whose element order means nothing and whose two equal elements are an error, like OCL's Set.
 */
export const set = <E extends z.ZodType>(element: E): CollectionSchema<E, "bag"> =>
  marked(element, setCheck as never, { kind: "set" });

/** The fields of `E` whose encoded value orders as their decoded one, which Lean's SortKey orders. */
type SortKeyOf<E extends z.ZodObject> = {
  [K in keyof E["shape"]]-?: E["shape"][K] extends typeof date
    ? K
    : E["shape"][K] extends { readonly _zod: { readonly def: { readonly type: "pipe" } } }
      ? never
      : z.output<E["shape"][K]> extends number
        ? K
        : never;
}[keyof E["shape"]] &
  string;

/** Lean's SortKey.of: the key that orders an encoded value, as a TS SortKey, whose compareKeys orders it as Lean. */
function encodedKey(json: unknown): SortKey | undefined {
  if (typeof json === "number") return json;
  return typeof json === "string" && date.safeParse(json).success ? (json as DateLabel) : undefined;
}

/** The key `key` of each element of a sortedBy array of `element`, read from its encoded value as Lean reads it. */
const keyOf = (element: z.ZodType, key: string) => (row: unknown) =>
  encodedKey((toJson(element, row) as Record<string, unknown> | null)?.[key]) as SortKey;

/**
 * Returns an array schema sorted ascending by `key`, like Kotlin's `sortedBy`. tazuna sorts the values that the spec
 * produces, so `resolve` and `decide` do not sort. A value from outside out of key order is an error (keyOrderIssue).
 */
export const sortedBy = <E extends z.ZodObject, K extends SortKeyOf<E>>(
  element: E,
  key: K,
): CollectionSchema<E, "sortedBy"> => marked(element, z.check(() => {}) as never, { kind: "sortedBy", key });

/** Returns the elements of a marked array that spec code made from Bags, or the value itself if it is no such array. */
function unbagged(collection: Collection | undefined, value: unknown): unknown {
  if (collection === undefined) return value;
  const values = bagValues(value);
  if (values !== undefined) return values;
  return collection.kind === "sortedBy" && Array.isArray(value) ? value.flatMap((v) => bagValues(v) ?? [v]) : value;
}

/** Lean's sortCollections. */
export function sortCollections(schema: unknown, v: Json): Json {
  const options = unionOptions(schema);
  if (options !== undefined) {
    const option = options.find((o) => fits(o, v));
    return option === undefined ? v : sortCollections(option, v);
  }
  if (Array.isArray(v)) {
    const item = field(schema, "items");
    const items = item === undefined ? v : v.map((x) => sortCollections(item, x));
    const sortedBy = field(schema, "x-tazuna-sorted-by");
    const unordered =
      typeof sortedBy === "string" || [field(schema, "x-tazuna-bag"), field(schema, "x-tazuna-set")].includes(true);
    if (!unordered) return items;
    const text = new Map(items.map((x) => [x, canonicalJson(x)]));
    const canonical = items.toSorted((a, b) => byCodePoint(text.get(a) as string, text.get(b) as string));
    if (typeof sortedBy !== "string") return canonical;
    const key = (x: Json) => encodedKey(field(x, sortedBy));
    return canonical.toSorted((a, b) => compareKeys(key(a), key(b)));
  }
  if (!isRecord(v)) return v;
  return Object.fromEntries(
    Object.entries(v).map(([k, x]) => {
      const child = field(field(schema, "properties"), k) ?? field(schema, "additionalProperties");
      return [k, child === undefined ? x : sortCollections(child, x as Json)];
    }),
  );
}

/**
 * Lean's keyOrdered, with where it fails: the first array of the encoded value `v` whose JSON Schema has
 * `x-tazuna-sorted-by` and whose elements are out of that key's order, as a Zod issue at the later element.
 */
export function keyOrderIssue(
  schema: unknown,
  v: Json,
  path: readonly PropertyKey[] = [],
): z.core.$ZodIssue | undefined {
  const options = unionOptions(schema);
  if (options !== undefined) {
    const option = options.find((o) => fits(o, v));
    return option === undefined ? undefined : keyOrderIssue(option, v, path);
  }
  if (Array.isArray(v)) {
    const item = field(schema, "items");
    for (const [i, x] of item === undefined ? [] : v.entries()) {
      const issue = keyOrderIssue(item, x, [...path, i]);
      if (issue !== undefined) return issue;
    }
    const key = field(schema, "x-tazuna-sorted-by");
    if (typeof key !== "string") return undefined;
    const keys = v.map((x) => encodedKey(field(x, key)));
    const i = keys.findIndex((k, i) => i > 0 && compareKeys(keys[i - 1], k) > 0);
    if (i < 0) return undefined;
    return {
      code: "custom",
      message: `element ${i} is before element ${i - 1} in ${key} order`,
      path: [...path, i],
    };
  }
  if (!isRecord(v)) return undefined;
  for (const [k, x] of Object.entries(v)) {
    const child = field(field(schema, "properties"), k) ?? field(schema, "additionalProperties");
    const issue = child === undefined ? undefined : keyOrderIssue(child, x as Json, [...path, k]);
    if (issue !== undefined) return issue;
  }
  return undefined;
}

/**
 * Returns a value from outside parsed by `schema`, which also lists each sortedBy array in key order as written
 * (keyOrderIssue), as Lean's Functions.parseOutside reads it.
 */
export function parsedOutside<T extends z.ZodType>(schema: T, value: unknown): z.ZodSafeParseResult<z.output<T>> {
  const parsed = schema.safeParse(value);
  if (!parsed.success) return parsed;
  const issue = keyOrderIssue(jsonSchema(schema), value as Json);
  return issue === undefined ? parsed : { success: false, error: new z.ZodError([issue]) as z.ZodError<z.output<T>> };
}

/**
 * Returns a value that spec code made for `schema` with each Bag in a bag or set, and each Bag or run of Bags in a
 * sortedBy array, as an array in the order that it holds its values, so that Zod can encode it.
 */
function arrayed(schema: z.ZodType, value: unknown): unknown {
  const node = schemaNode(schema);
  switch (node.type) {
    case "array": {
      const array = unbagged(collectionOf(schema), value);
      return Array.isArray(array) ? array.map((v) => arrayed(node.element, v)) : array;
    }
    case "object":
      if (!isRecord(value)) return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => {
          const field = fieldSchema(node, k);
          return [k, field === undefined ? v : arrayed(field, v)];
        }),
      );
    case "union": {
      const option = unionOption(node, value);
      return option === undefined ? value : arrayed(option, value);
    }
    case "optional":
    case "nullable":
    case "default":
      return value == null ? value : arrayed(node.inner, value);
    default:
      return value;
  }
}

/**
 * Returns a value that spec code made for `schema` as JSON holds it, in the order it was built, or why a part does not
 * encode. Each codec encodes its part as Zod does, checking what it takes; no other check runs, since the run checks a
 * value after it sorts it (Lean's Functions.sorting).
 */
export function encoded(
  schema: z.ZodType,
  value: unknown,
): { readonly encoded: Json } | { readonly error: z.ZodError } {
  const issues: z.core.$ZodIssue[] = [];
  const json = codecsEncoded(schema, arrayed(schema, value), [], issues);
  return issues.length === 0 ? { encoded: plain(json) } : { error: new z.ZodError(issues) };
}

/** toJson with each codec encoding as Zod does, which adds to `issues`, at `path`, what its part fails. */
function codecsEncoded(
  schema: z.ZodType,
  value: unknown,
  path: readonly PropertyKey[],
  issues: z.core.$ZodIssue[],
): unknown {
  const node = schemaNode(schema);
  const at = (child: z.ZodType, v: unknown, key: PropertyKey) => codecsEncoded(child, v, [...path, key], issues);
  switch (node.type) {
    case "codec": {
      const wire = z.safeEncode(schema, value as never);
      if (wire.success) return wire.data;
      issues.push(...wire.error.issues.map((issue) => ({ ...issue, path: [...path, ...issue.path] })));
      return value;
    }
    case "pipe":
      return codecsEncoded(node.in, codecsEncoded(node.out, value, path, issues), path, issues);
    case "array":
      return Array.isArray(value) ? value.map((v, i) => at(node.element, v, i)) : value;
    case "tuple":
      if (!Array.isArray(value)) return value;
      return value.map((v, i) => {
        const item = node.items[i] ?? node.rest;
        return item === undefined ? v : at(item, v, i);
      });
    case "object":
      if (!isRecord(value)) return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => {
          const field = fieldSchema(node, k);
          return [k, field === undefined ? v : at(field, v, k)];
        }),
      );
    case "record":
      if (!isRecord(value)) return value;
      return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, at(node.value, v, k)]));
    case "union": {
      const option = unionOption(node, value);
      return option === undefined ? value : codecsEncoded(option, value, path, issues);
    }
    case "intersection":
      return codecsEncoded(node.right, codecsEncoded(node.left, value, path, issues), path, issues);
    case "lazy":
      return codecsEncoded(node.inner, value, path, issues);
    case "opaque":
      return value == null || node.inner === undefined ? value : codecsEncoded(node.inner, value, path, issues);
    default:
      return value == null ? value : codecsEncoded(node.inner, value, path, issues);
  }
}

/** Returns a value of `schema` from its checked encoding, as spec code receives it. */
export const decoded = (schema: z.ZodType, json: unknown): unknown => bagged(schema, fromJson(schema, json));

/** Whether `arrayed` and `bagged` walk into the node. A collection under any other node is opaque. */
export const sortsInside = (node: SchemaNode): boolean =>
  ["array", "object", "union", "optional", "nullable", "default"].includes(node.type);

const optionSchemas = new WeakMap<readonly z.ZodType[], readonly JsonSchema[]>();

/**
 * Returns the option of a union that `value` takes by Lean's `fits`, read from the JSON Schema of each option: the
 * first that fits, if any. A plain union holds no codec, so the encoded value that `fits` reads differs from `value`
 * only by its Bags, which `fits` reads as arrays.
 */
export function unionOption(node: Extract<SchemaNode, { type: "union" }>, value: unknown): z.ZodType | undefined {
  const known = optionSchemas.get(node.options);
  const schemas = known ?? node.options.map(jsonSchema);
  if (known === undefined) optionSchemas.set(node.options, schemas);
  const i = schemas.findIndex((schema) => fits(schema, value));
  return i < 0 ? undefined : node.options[i];
}

/**
 * Returns a value of `schema` that a parse took as JSON holds it: each codec at any depth encodes its part, and no check
 * or other transform runs.
 */
export function toJson(schema: z.ZodType, value: unknown): unknown {
  const node = schemaNode(schema);
  switch (node.type) {
    case "codec": {
      const wire = node.encode(toJson(node.out, value));
      if (wire === undefined) throw new InternalError("a codec did not encode a value that parse took");
      return toJson(node.in, wire.value);
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
      const option = unionOption(node, value);
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

/**
 * Returns a value of `schema` from the JSON that toJson wrote of it: the mirror of toJson, which runs only the decode
 * of each codec. The value was checked when it was parsed, so no check runs again.
 */
export function fromJson(schema: z.ZodType, json: unknown): unknown {
  const node = schemaNode(schema);
  switch (node.type) {
    case "codec": {
      const value = node.decode(fromJson(node.in, json));
      if (value === undefined) throw new InternalError("a codec did not decode a checked encoding");
      return fromJson(node.out, value.value);
    }
    case "pipe":
      return fromJson(node.out, fromJson(node.in, json));
    case "array":
      return Array.isArray(json) ? json.map((v) => fromJson(node.element, v)) : json;
    case "tuple":
      if (!Array.isArray(json)) return json;
      return json.map((v, i) => {
        const item = node.items[i] ?? node.rest;
        return item === undefined ? v : fromJson(item, v);
      });
    case "object":
      if (!isRecord(json)) return json;
      return Object.fromEntries(
        Object.entries(json).map(([k, v]) => {
          const field = fieldSchema(node, k);
          return [k, field === undefined ? v : fromJson(field, v)];
        }),
      );
    case "record":
      if (!isRecord(json)) return json;
      return Object.fromEntries(Object.entries(json).map(([k, v]) => [k, fromJson(node.value, v)]));
    case "union": {
      const option = unionOption(node, json);
      return option === undefined ? json : fromJson(option, json);
    }
    case "intersection":
      return fromJson(node.left, fromJson(node.right, json));
    case "lazy":
      return fromJson(node.inner, json);
    case "opaque":
      return json == null || node.inner === undefined ? json : fromJson(node.inner, json);
    default:
      return json == null ? json : fromJson(node.inner, json);
  }
}

const isRecord = (value: unknown): value is Readonly<Record<string, unknown>> =>
  value !== null && typeof value === "object" && !Array.isArray(value);

/**
 * Returns a decoded value whose collections the run sorted as spec code receives it: each bag and set as a Bag, and each
 * sortedBy array as Runs.
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
      return runsOf(items, keyOf(node.element, collection.key)).map((run) => new BagValue(() => run));
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
      const option = unionOption(node, value);
      return option === undefined ? value : bagged(option, value);
    }
    case "optional":
    case "nullable":
    case "default":
      return value == null ? value : bagged(node.inner, value);
    default:
      return value;
  }
}

/** Returns the default value of each field of the shape that declares one, in the order it was built. */
export function defaultRow(shape: Shape): Fields {
  return Object.fromEntries(
    Object.entries(shape as Readonly<Record<string, z.ZodType>>).flatMap(([field, schema]) => {
      const defaulted = schema.safeParse(undefined);
      return defaulted.success && defaulted.data !== undefined ? [[field, defaulted.data] as const] : [];
    }),
  );
}
