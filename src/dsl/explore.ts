import type { z } from "zod";

/** The values that explore gives the inputs of one schema, which `domain()` returns. */
export interface Domain {
  readonly schema: z.ZodType;
  readonly values: readonly unknown[];
}

/**
 * The values `values` for every input that explore writes where the spec writes `schema`, or, for an entity's key or
 * `ref()`, any schema of that entity's key. A boolean, an enum, a literal, null, and an optional field's absence need
 * no domain.
 */
export const domain = <S extends z.ZodType>(schema: S, values: readonly z.input<S>[]): Domain => ({ schema, values });

/** The bounds of the paths that `test` explores after the scenarios of the service named `service`. */
export interface Explore {
  readonly service: string;
  /** The most moves on a path after a scenario. */
  readonly depth: number;
  readonly domains: readonly Domain[];
}

const explores = new WeakSet<object>();

/**
 * Defines the paths that `test` explores after each scenario of the service named `service`: every move that the
 * world enables, each input written from `domains`, up to `depth` moves. The name is written rather than taken from
 * the service's definer, as `constants()` does.
 */
export function explore(options: Explore): Explore {
  if (!Number.isInteger(options.depth) || options.depth < 0)
    throw new RangeError(`explore() of ${options.service}: depth ${options.depth} is not a non-negative integer`);
  const defined = Object.freeze({ ...options });
  explores.add(defined);
  return defined;
}

export const isExplore = (value: unknown): value is Explore =>
  typeof value === "object" && value !== null && explores.has(value);
