import { z } from "zod";
import type { Bag, Made, MarkOf, Runs } from "../data/bag.ts";
import type { Shape } from "../data/values.ts";
import type { Conditions, Named } from "./conditions.ts";

export type DefaultedShape = Readonly<Record<string, z.ZodDefault<z.ZodType>>>;
/** The type T with every nested object and array readonly, each bag and set a Bag, and each sortedBy array Runs. */
export type Immutable<T> = T extends Temporal.Instant | Temporal.PlainDate | Temporal.Duration
  ? T
  : T extends readonly (infer E)[]
    ? [MarkOf<T>] extends [never]
      ? readonly Immutable<E>[]
      : MarkOf<T> extends "sortedBy"
        ? Runs<Immutable<E>>
        : Bag<Immutable<E>>
    : T extends object
      ? { readonly [K in keyof T]: Immutable<T[K]> }
      : T;

/** A record's values as expressions receive them; changing one is a type error. */
export type Row<S extends Shape> = Immutable<z.output<z.ZodObject<{ -readonly [K in keyof S]: S[K] }>>>;
/** Values of shape `S` as expressions return them: a bag, set or sortedBy field also takes a Bag. */
export type MadeRow<S extends Shape> = Made<Row<S>>;

export interface KeyedEntity<S extends Shape = Shape, K extends keyof S & string = keyof S & string> {
  readonly kind: "entity";
  readonly single: false;
  readonly description: string;
  readonly fields: S;
  readonly key: K;
  readonly unique: readonly (keyof S & string)[];
  readonly invariants: Conditions<{ record: Row<S> }>;
}

export interface SingleEntity<S extends Shape = Shape> {
  readonly kind: "entity";
  readonly single: true;
  readonly description: string;
  readonly fields: S;
  readonly invariants: Conditions<{ record: Row<S> }>;
}

// biome-ignore lint/suspicious/noExplicitAny: an entity of any shape
export type AnyKeyedEntity = KeyedEntity<any, any>;
// biome-ignore lint/suspicious/noExplicitAny: an entity of any shape
export type AnyEntity = AnyKeyedEntity | SingleEntity<any>;
export type KeyOf<E extends AnyKeyedEntity> = E extends { readonly key: infer K extends string } ? K : never;
export type KeyValue<E extends AnyKeyedEntity> =
  E extends KeyedEntity<infer S, infer K> ? Row<S>[K & keyof Row<S>] : never;
/** A record of `E` as expressions receive it, for helpers that take records (like Drizzle's InferSelectModel). */
export type RowOf<E extends AnyEntity> =
  E extends KeyedEntity<infer S> ? Row<S> : E extends SingleEntity<infer S> ? Row<S> : never;

/**
 * Defines the shape of records identified by `key`. Other definitions reuse a field's schema as `Task.fields.title`.
 */
export function entity<
  const S extends Shape,
  const K extends keyof S & string,
  const Iv extends string = never,
>(definition: {
  description: string;
  /** A field that can be null is `.nullable()`. */
  fields: S;
  /** The key field, whose value never changes after the record is created. */
  key: K;
  /** The fields whose combined values no two records share; a record with null in any of them is not checked. */
  unique?: readonly (keyof S & string)[];
  /** The conditions that every record meets (Fault.failedEntityInvariant). */
  invariants?: Named<Iv, { record: Row<S> }>;
}): KeyedEntity<S, K> {
  return {
    kind: "entity",
    single: false,
    description: definition.description,
    fields: definition.fields,
    key: definition.key,
    unique: definition.unique ?? [],
    invariants: (definition.invariants ?? {}) as Conditions<{ record: Row<S> }>,
  };
}

/** Defines an entity with exactly one record; `records.Settings` is that record. */
export function singleEntity<const S extends DefaultedShape, const Iv extends string = never>(definition: {
  description: string;
  fields: S;
  /** The conditions that the record meets (Fault.failedSingleInvariant). */
  invariants?: Named<Iv, { record: Row<S> }>;
}): SingleEntity<S> {
  return {
    kind: "entity",
    single: true,
    description: definition.description,
    fields: definition.fields,
    invariants: (definition.invariants ?? {}) as Conditions<{ record: Row<S> }>,
  };
}

const refTargets = new WeakMap<z.ZodType, AnyKeyedEntity>();
declare const refEntity: unique symbol;

export type Ref<E extends AnyKeyedEntity> = z.ZodType<KeyValue<E>, KeyValue<E>> & { readonly [refEntity]: E };

/** Returns the schema of a field whose value is the key of a `target` record. */
export function ref<E extends AnyKeyedEntity>(target: E): Ref<E> {
  const schema = (target.fields[target.key] as z.ZodType).clone();
  refTargets.set(schema, target);
  return schema as Ref<E>;
}

export function refTarget(schema: z.ZodType): AnyKeyedEntity | undefined {
  const direct = refTargets.get(schema);
  if (direct !== undefined) return direct;
  if (schema instanceof z.ZodNullable || schema instanceof z.ZodDefault) return refTarget(schema.unwrap() as z.ZodType);
  return undefined;
}

export type Entities = Readonly<Record<string, AnyEntity>>;

/** The records of a keyed entity, without order. */
interface Table<E extends AnyKeyedEntity> extends Bag<RowOf<E>> {
  get(key: KeyValue<E>): RowOf<E> | undefined;
}

/** A table per keyed entity; the record itself per single entity. */
export type Records<Es extends Entities> = {
  readonly [N in keyof Es]: Es[N] extends AnyKeyedEntity
    ? Table<Es[N]>
    : Es[N] extends SingleEntity<infer S>
      ? Row<S>
      : never;
};
