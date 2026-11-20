import { z } from "zod";
import { strict } from "./schemaNode.ts";

export type Shape = Readonly<Record<string, z.ZodType>>;
export type Fields = Record<string, unknown>;

const objects = new WeakMap<Shape, z.ZodObject>();
const strictObjects = new WeakMap<Shape, z.ZodObject>();

function cached(
  cache: WeakMap<Shape, z.ZodObject>,
  shape: Shape,
  make: (shape: Record<string, z.ZodType>) => z.ZodObject,
): z.ZodObject {
  let o = cache.get(shape);
  if (o === undefined) {
    o = make(shape as Record<string, z.ZodType>);
    cache.set(shape, o);
  }
  return o;
}

export const objectOf = (shape: Shape): z.ZodObject => cached(objects, shape, z.object);

export const strictObjectOf = (shape: Shape): z.ZodObject =>
  cached(strictObjects, shape, (s) => strict(z.object(s)) as z.ZodObject);

/** Orders strings by code point, as Lean's String order does; `<` on strings compares UTF-16 code units. */
export function byCodePoint(a: string, b: string): number {
  let i = 0;
  while (i < a.length && i < b.length) {
    const [x, y] = [a.codePointAt(i) as number, b.codePointAt(i) as number];
    if (x !== y) return x - y;
    i += x > 0xffff ? 2 : 1;
  }
  return a.length - b.length;
}

/**
 * Returns the JSON text of `value` with object keys in code point order, as in Lean's Value.canonical, so that equal
 * values have the same text.
 */
export function canonicalJson(value: unknown): string {
  if (Array.isArray(value)) return `[${value.map(canonicalJson).join(",")}]`;
  if (value === null || typeof value !== "object") return JSON.stringify(value) ?? "null";
  if ("toJSON" in value && typeof value.toJSON === "function") return canonicalJson(value.toJSON());
  const fields = value as Record<string, unknown>;
  const keys = Object.keys(fields).filter((k) => fields[k] !== undefined);
  return `{${keys
    .toSorted(byCodePoint)
    .map((k) => `${JSON.stringify(k)}:${canonicalJson(fields[k])}`)
    .join(",")}}`;
}

/** Whether two values are equal as JSON, objects compared without regard to key order. */
// biome-ignore lint/plugin: the one place that defines JSON equality
export const sameJson = (a: unknown, b: unknown): boolean => canonicalJson(a) === canonicalJson(b);

export type Json = string | number | boolean | null | readonly Json[] | { readonly [key: string]: Json };

export const plain = (value: unknown): Json => JSON.parse(JSON.stringify(value) ?? "null") as Json;

/** Lean's Value.strings: the strings of `value`, excluding object field names, in order. */
export function stringsOf(value: unknown): string[] {
  if (typeof value === "string") return [value];
  if (value !== null && typeof value === "object") return Object.values(value).flatMap(stringsOf);
  return [];
}

/** Lean's Value.mapStrings: `value` with each string, excluding object field names, mapped by `f`. */
export function mapStrings(value: unknown, f: (s: string) => string): unknown {
  if (typeof value === "string") return f(value);
  if (Array.isArray(value)) return value.map((v) => mapStrings(v, f));
  if (value !== null && typeof value === "object")
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, mapStrings(v, f)]));
  return value;
}

/** Lean's Value.overlay: `value` with the fields of `over` in place, at any depth; any value but an object replaces. */
export function overlay(value: unknown, over: unknown): unknown {
  const isObject = (v: unknown): v is Record<string, unknown> =>
    v !== null && typeof v === "object" && !Array.isArray(v);
  if (!isObject(value) || !isObject(over)) return over;
  return Object.fromEntries([
    ...Object.entries(value).map(([k, v]) => [k, Object.hasOwn(over, k) ? overlay(v, over[k]) : v]),
    ...Object.entries(over).filter(([k]) => !Object.hasOwn(value, k)),
  ]);
}
