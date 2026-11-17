import type { z } from "zod";
import type { Shape } from "../data/values.ts";
import type { AnyKeyedEntity, Entities, KeyedEntity, SingleEntity } from "./entity.ts";

/** A record as a Given writes it: every field, in trace form. */
type GivenRow<S extends Shape> = { readonly [K in keyof S]-?: z.input<S[K]> };

/** The records of a service as data: every record of a keyed entity, and the record of a single entity. */
export type RecordsData<Es extends Entities> = {
  readonly [N in keyof Es]: Es[N] extends AnyKeyedEntity
    ? Es[N] extends KeyedEntity<infer S>
      ? readonly GivenRow<S>[]
      : never
    : Es[N] extends SingleEntity<infer S>
      ? GivenRow<S>
      : never;
};

declare const contractFacts: unique symbol;

/**
 * A contract: its members, and, as types only, the records of its service, whether tazuna runs the service's spec
 * (`spec`) or takes the service as contract only (`external`), and the service's name `N`.
 */
export type Contract<M, R, K extends "spec" | "external", N extends string = string> = M & {
  readonly [contractFacts]: { readonly records: R; readonly kind: K; readonly service: N };
};

/** The records of the service of contract `C`. */
export type RecordsOf<C> = C extends Contract<unknown, infer R, "spec" | "external"> ? R : never;

/** Whether tazuna runs the spec of the service of contract `C` (`spec`) or takes it as contract only (`external`). */
export type KindOf<C> = C extends Contract<unknown, unknown, infer K> ? K : never;

/** The name of the service of contract `C`. */
export type ServiceOf<C> = C extends Contract<unknown, unknown, "spec" | "external", infer N> ? N : never;
