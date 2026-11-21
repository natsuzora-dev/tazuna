import type { z } from "zod";

declare const made: unique symbol;

/** The values that explore gives the nodes that one schema names, which only `domain()` makes. */
export interface Domain {
  readonly [made]: true;
  readonly schema: z.ZodType;
  readonly values: readonly unknown[];
}

/**
 * The values `values` for every node that explore writes where the spec writes `schema`, the same Zod object, in any
 * schema that a move of the explored service may carry: the input of an own command or query, the output of another
 * service's command or query that the service sends (every other service may be external in some scenario, so this
 * includes a peer that always runs), the payload of another service's event that the service receives, and the payload
 * of a control that an own screen offers as `any`.
 *
 * - A domain sees through `optional`, `default`, `lazy`, and a codec's or pipe's input. An optional field, or one with a
 *   default, is also left out.
 * - On a `nullable`, a domain names the non-null option, and null is a value of its own.
 * - A domain on a key schema of an entity, its key field or a `ref()` of it, names every key of that entity.
 * - A domain names a whole array or record, and nothing inside one unless the domain names it whole.
 * - A domain names a whole object too: explore writes its values whole and reads no domain inside it.
 * - A boolean, an enum, a literal, and null enumerate themselves, and a domain on one narrows it. Every other node needs
 *   a domain, or `check` reports `Illegal.undeclaredDomain`.
 *
 * A domain that names no node is `Malformed.unusedDomain`. Two domains that name one node, or one node and a node
 * inside it, are `Malformed.overlappingDomain`. A value that `schema` rejects, refinements included, is
 * `Malformed.domainValue`.
 */
export const domain = <S extends z.ZodType>(schema: S, values: readonly Exclude<z.input<S>, undefined>[]): Domain =>
  ({ schema, values }) as unknown as Domain;

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
 * world enables, each value written from `domains`, up to `depth` moves.
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
