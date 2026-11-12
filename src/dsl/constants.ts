import type { z } from "zod";
import type { Immutable } from "./entity.ts";

const schemas = new WeakMap<object, z.ZodObject>();
declare const grouped: unique symbol;

export type ConstantsGroup<T = unknown> = T & { readonly [grouped]: true };

/** Defines the constants of a service, parsed with `schema`. A length of time is a `duration` field. */
export function constants<const S extends z.ZodObject>(
  schema: S,
  values: z.input<S>,
): ConstantsGroup<Immutable<z.output<S>>> {
  const parsed = Object.freeze(schema.parse(values));
  schemas.set(parsed, schema);
  return parsed as ConstantsGroup<Immutable<z.output<S>>>;
}

export const constantsSchema = (value: unknown): z.ZodObject | undefined =>
  typeof value === "object" && value !== null ? schemas.get(value) : undefined;
