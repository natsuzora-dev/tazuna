import type { z } from "zod";

const schemas = new WeakMap<object, z.ZodObject>();
declare const grouped: unique symbol;

export type ConstantsGroup<T = unknown> = T & { readonly [grouped]: true };

/** The type T with every nested object and array readonly; a bag stays an array, since implementations read it too. */
type Frozen<T> = T extends Temporal.Instant | Temporal.PlainDate | Temporal.Duration
  ? T
  : T extends readonly (infer E)[]
    ? readonly Frozen<E>[]
    : T extends object
      ? { readonly [K in keyof T]: Frozen<T[K]> }
      : T;

/** Defines the constants of a service, parsed with `schema`. A length of time is a `duration` field. */
export function constants<const S extends z.ZodObject>(
  schema: S,
  values: z.input<S>,
): ConstantsGroup<Frozen<z.output<S>>> {
  const parsed = Object.freeze(schema.parse(values));
  schemas.set(parsed, schema);
  return parsed as ConstantsGroup<Frozen<z.output<S>>>;
}

export const constantsSchema = (value: unknown): z.ZodObject | undefined =>
  typeof value === "object" && value !== null ? schemas.get(value) : undefined;
