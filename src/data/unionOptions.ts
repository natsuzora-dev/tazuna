import { BagValue } from "./bag.ts";
import { sameJson } from "./values.ts";

const isObject = (v: unknown): v is Readonly<Record<string, unknown>> =>
  v !== null && typeof v === "object" && !Array.isArray(v) && !(v instanceof BagValue);

/** Lean's Value.field?: a field that is undefined is absent, as JSON writes it. */
export const field = (v: unknown, key: string): unknown => (isObject(v) && Object.hasOwn(v, key) ? v[key] : undefined);

/** Lean's unionOptions. */
export function unionOptions(schema: unknown): readonly unknown[] | undefined {
  const anyOf = field(schema, "anyOf");
  if (Array.isArray(anyOf)) return anyOf;
  const oneOf = field(schema, "oneOf");
  return Array.isArray(oneOf) ? oneOf : undefined;
}

/** Lean's typeNames, of a JSON value or of a value as spec code holds it, whose Bag is an array. */
function typeNames(v: unknown): readonly string[] {
  if (v === null) return ["null"];
  if (Array.isArray(v) || v instanceof BagValue) return ["array"];
  switch (typeof v) {
    case "boolean":
      return ["boolean"];
    case "number":
      return ["number", "integer"];
    case "string":
      return ["string"];
    case "object":
      return ["object"];
    default:
      return [];
  }
}

/** Lean's fitsType. */
function fitsType(schema: unknown, v: unknown): boolean {
  const type = field(schema, "type");
  if (type === undefined) return true;
  if (typeof type === "string") return typeNames(v).includes(type);
  return Array.isArray(type) && type.some((t) => typeof t === "string" && typeNames(v).includes(t));
}

/** Lean's allowed. */
function allowed(schema: unknown): readonly unknown[] | undefined {
  if (isObject(schema) && Object.hasOwn(schema, "const")) return [schema["const"]];
  const values = field(schema, "enum");
  return Array.isArray(values) ? values : undefined;
}

const admits = (schema: unknown, v: unknown): boolean => allowed(schema)?.some((c) => sameJson(c, v)) ?? true;

const requiredOf = (schema: unknown): string[] => {
  const required = field(schema, "required");
  return Array.isArray(required) ? required.filter((k): k is string => typeof k === "string") : [];
};

const propertyOf = (schema: unknown, k: string): unknown => field(field(schema, "properties"), k);

const closed = (schema: unknown): boolean => field(schema, "additionalProperties") === false;

/** Lean's fits. */
export function fits(option: unknown, v: unknown): boolean {
  if (!fitsType(option, v) || !admits(option, v)) return false;
  if (!isObject(v)) return true;
  return (
    Object.entries(v).every(([k, x]) => {
      if (x === undefined) return true;
      const p = propertyOf(option, k);
      return p === undefined ? !closed(option) : admits(p, x);
    }) && requiredOf(option).every((k) => field(v, k) !== undefined)
  );
}
