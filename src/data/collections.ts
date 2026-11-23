import { z } from "zod";
import type { Marked } from "./bag.ts";
import { type JsonSchema, jsonSchema } from "./jsonSchema.ts";
import { type Collection, mark } from "./marks.ts";
import { fieldSchema, type SchemaNode, schemaNode } from "./schemaNode.ts";
import type { date } from "./time.ts";
import { fits } from "./unionOptions.ts";
import { canonicalJson, type Fields, type Json, plain, type Shape } from "./values.ts";

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

/**
 * Returns an array schema sorted ascending by `key`, like Kotlin's `sortedBy`. tazuna sorts the values that the spec
 * produces, so `resolve` and `decide` do not sort. A value from outside out of key order is an error.
 */
export const sortedBy = <E extends z.ZodObject, K extends SortKeyOf<E>>(
  element: E,
  key: K,
): CollectionSchema<E, "sortedBy"> => marked(element, z.check(() => {}) as never, { kind: "sortedBy", key });

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
  const json = codecsEncoded(schema, value, [], issues);
  return issues.length === 0 ? { encoded: plain(json) } : { error: new z.ZodError(issues) };
}

/** `value` as JSON holds it, each codec encoding as Zod does and adding to `issues`, at `path`, what its part fails. */
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

/** Whether the run sorts the collections inside the node (Lean's Functions.sorting). Any other node is opaque. */
export const sortsInside = (node: SchemaNode): boolean =>
  ["array", "object", "union", "optional", "nullable", "default"].includes(node.type);

const optionSchemas = new WeakMap<readonly z.ZodType[], readonly JsonSchema[]>();

/**
 * Returns the option of a union that `value` takes by Lean's `fits`, read from the JSON Schema of each option: the
 * first that fits, if any. A plain union holds no codec, so `fits` reads `value` as its encoding.
 */
function unionOption(node: Extract<SchemaNode, { type: "union" }>, value: unknown): z.ZodType | undefined {
  const known = optionSchemas.get(node.options);
  const schemas = known ?? node.options.map(jsonSchema);
  if (known === undefined) optionSchemas.set(node.options, schemas);
  const i = schemas.findIndex((schema) => fits(schema, value));
  return i < 0 ? undefined : node.options[i];
}

const isRecord = (value: unknown): value is Readonly<Record<string, unknown>> =>
  value !== null && typeof value === "object" && !Array.isArray(value);

/** Returns the default value of each field of the shape that declares one, in the order it was built. */
export function defaultRow(shape: Shape): Fields {
  return Object.fromEntries(
    Object.entries(shape as Readonly<Record<string, z.ZodType>>).flatMap(([field, schema]) => {
      const defaulted = schema.safeParse(undefined);
      return defaulted.success && defaulted.data !== undefined ? [[field, defaulted.data] as const] : [];
    }),
  );
}
