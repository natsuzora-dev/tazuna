import { z } from "zod";
import { collectionOf } from "../data/collections.ts";
import { date, datetime } from "../data/datetime.ts";
import { canonicalJson, objectOf, type Shape } from "../data/values.ts";

export const stringsIn = (value: unknown): string[] =>
  typeof value === "string"
    ? [value]
    : value !== null && typeof value === "object"
      ? Object.values(value).flatMap(stringsIn)
      : [];

const none = Symbol("none");

/**
 * Returns the `i`th representative value of `schema`, or `none` for an unhandled schema kind. Strings come from the
 * scenario's words so that they can reach the values that guards compare.
 */
function representative(schema: z.ZodType, words: readonly string[], i: number): unknown {
  if (schema === datetime) return ["2026-10-25T00:00:00Z", "2026-10-26T00:00:00Z"][i % 2];
  if (schema === date) return ["2026-10-25", "2026-10-26"][i % 2];
  if (schema instanceof z.ZodNullable)
    return i % 2 === 1 ? null : representative(schema.unwrap() as z.ZodType, words, i);
  if (schema instanceof z.ZodOptional || schema instanceof z.ZodDefault)
    return representative(schema.def.innerType as z.ZodType, words, i);
  if (schema instanceof z.ZodBoolean) return i % 2 === 1;
  if (schema instanceof z.ZodEnum) {
    const options = schema.options as readonly unknown[];
    return options[i % options.length];
  }
  if (schema instanceof z.ZodLiteral) {
    const values = [...schema.values];
    return values[i % values.length];
  }
  if (schema instanceof z.ZodUnion) {
    const options = schema.options as readonly z.ZodType[];
    return representative(options[i % options.length] as z.ZodType, words, i);
  }
  if (schema instanceof z.ZodArray) {
    if (i === 0) return [];
    const element = representative(schema.element as z.ZodType, words, i - 1);
    return element === none || collectionOf(schema)?.kind === "sortedBy" ? [] : [element];
  }
  if (schema instanceof z.ZodString) {
    const fits = [...words, "a", "b", "c"].filter((s) => schema.safeParse(s).success);
    return fits.length === 0 ? none : fits[i % fits.length];
  }
  if (schema instanceof z.ZodNumber) {
    const fits = [0, 1, 2, -1, 0.5, 10, 1000].filter((n) => schema.safeParse(n).success);
    return fits.length === 0 ? none : fits[i % fits.length];
  }
  if (schema instanceof z.ZodObject) return objectRepresentative(schema.shape as Shape, words, i);
  return none;
}

function objectRepresentative(shape: Shape, words: readonly string[], i: number): unknown {
  const entries = Object.entries(shape).map(([k, s]) => [k, representative(s, words, i)] as const);
  return entries.some(([, v]) => v === none) ? none : Object.fromEntries(entries);
}

export function valuesFor(shape: Shape, listed: readonly unknown[], words: readonly string[], n: number): unknown[] {
  const found = new Map<string, unknown>();
  for (const v of listed) found.set(canonicalJson(v), v);
  for (let i = 0; found.size < n && i < n + 2; i += 1) {
    const v = objectRepresentative(shape, words, i);
    if (v !== none && objectOf(shape).safeParse(v).success) found.set(canonicalJson(v), v);
  }
  return [...found.values()].slice(0, n);
}
