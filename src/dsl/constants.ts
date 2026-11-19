import type { z } from "zod";

const schemas = new WeakMap<object, z.ZodObject>();
const services = new WeakMap<object, string>();
declare const grouped: unique symbol;

export type ConstantsGroup<T = unknown> = T & { readonly [grouped]: true };

/** The type T with every nested object and array readonly. A bag stays an array, since implementations read it too. */
type Frozen<T> = T extends Temporal.Instant | Temporal.PlainDate | Temporal.Duration
  ? T
  : T extends readonly (infer E)[]
    ? readonly Frozen<E>[]
    : T extends object
      ? { readonly [K in keyof T]: Frozen<T[K]> }
      : T;

/**
 * Defines the constants of the service named `service`, parsed with `schema`. A length of time is a `duration` field.
 * The name is written rather than taken from the service's definer, because entities, which the definer lists, may read
 * the constants.
 */
export function constants<const S extends z.ZodObject>({
  service,
  schema,
  values,
}: {
  service: string;
  schema: S;
  values: z.input<S>;
}): ConstantsGroup<Frozen<z.output<S>>> {
  const parsed = Object.freeze(schema.parse(values));
  schemas.set(parsed, schema);
  services.set(parsed, service);
  return parsed as ConstantsGroup<Frozen<z.output<S>>>;
}

/** The name of the service that the constants `value` belong to. */
export const constantsService = (value: unknown): string | undefined =>
  typeof value === "object" && value !== null ? services.get(value) : undefined;

export const constantsSchema = (value: unknown): z.ZodObject | undefined =>
  typeof value === "object" && value !== null ? schemas.get(value) : undefined;
