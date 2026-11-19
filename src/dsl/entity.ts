import { z } from "zod";
import type { Bag, Made, MarkOf, Runs } from "../data/bag.ts";
import { childrenOf, schemaNode } from "../data/schemaNode.ts";
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

const refTargets = new WeakMap<z.ZodType, AnyKeyedEntity>();
const keyFieldOwners = new WeakMap<z.ZodType, AnyKeyedEntity>();
/** Each `ref.self()` placeholder, with the key schema that it reads once `entity()` has claimed it. */
const selfRefs = new WeakMap<z.ZodType, { key?: z.ZodType }>();

declare const selfMark: unique symbol;
type SelfRef = z.ZodType<unknown, unknown> & { readonly [selfMark]: true };
/** `T` with each `ref.self()` in it, alone or under nullable, optional, default or array, as the key schema `Key`. */
type Resolved<T, Key extends z.ZodType> = T extends SelfRef
  ? Key
  : T extends z.ZodNullable<infer I extends z.ZodType>
    ? z.ZodNullable<Resolved<I, Key>>
    : T extends z.ZodOptional<infer I extends z.ZodType>
      ? z.ZodOptional<Resolved<I, Key>>
      : T extends z.ZodDefault<infer I extends z.ZodType>
        ? z.ZodDefault<Resolved<I, Key>>
        : T extends z.ZodArray<infer I extends z.ZodType>
          ? z.ZodArray<Resolved<I, Key>>
          : T;
type SelfResolved<S extends Shape, K extends keyof S> = { [F in keyof S]: Resolved<S[F], S[K]> };

/** Returns the unclaimed `ref.self()` placeholders in `schema`. */
function unclaimedSelfRefs(schema: z.ZodType, seen = new Set<z.ZodType>()): z.ZodType[] {
  if (seen.has(schema)) return [];
  seen.add(schema);
  const self = selfRefs.get(schema);
  if (self !== undefined) return self.key === undefined ? [schema] : [];
  return childrenOf(schemaNode(schema)).flatMap((child) => unclaimedSelfRefs(child, seen));
}

/**
 * Defines the shape of records identified by `key`. Other definitions reuse a field's schema as `Task.fields.title`.
 */
export function entity<
  const S extends Shape,
  const K extends keyof S & string,
  const Iv extends string = never,
>(definition: {
  description: string;
  /** A field that can be null is `.nullable()`. A field that holds the key of a record of this entity is `ref.self()`. */
  fields: S;
  /** The key field, whose value never changes after the record is created. */
  key: K;
  /** The fields whose combined values no two records share; a record with null in any of them is not checked. */
  unique?: readonly (keyof S & string)[];
  /** The conditions that every record meets (Fault.failedEntityInvariant). */
  invariants?: Named<Iv, { record: Row<SelfResolved<S, K>> }>;
}): KeyedEntity<SelfResolved<S, K>, K> {
  // A clone, so that a schema that the key field shares with other fields does not mark them as key positions too.
  const shared = definition.fields[definition.key] as z.ZodType;
  if (selfRefs.has(shared)) throw new TypeError("The key field of an entity cannot be ref.self()");
  const key = shared.clone();
  const target = refTargets.get(shared);
  if (target !== undefined) refTargets.set(key, target);
  const keyed: KeyedEntity<SelfResolved<S, K>, K> = {
    kind: "entity",
    single: false,
    description: definition.description,
    fields: { ...definition.fields, [definition.key]: key } as unknown as SelfResolved<S, K>,
    key: definition.key,
    unique: definition.unique ?? [],
    invariants: (definition.invariants ?? {}) as Conditions<{ record: Row<SelfResolved<S, K>> }>,
  };
  keyFieldOwners.set(key, keyed);
  for (const field of Object.values(definition.fields) as z.ZodType[])
    for (const self of unclaimedSelfRefs(field)) {
      selfRefs.set(self, { key });
      refTargets.set(self, keyed);
    }
  return keyed;
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

declare const refEntity: unique symbol;

export type Ref<E extends AnyKeyedEntity> = z.ZodType<KeyValue<E>, KeyValue<E>> & { readonly [refEntity]: E };

/**
 * Returns the schema of a field whose value is the key of a `target` record. `test` and `verify` compare a created key
 * up to renaming only where its schema is `ref(target)`, `ref.self()`, or `target`'s key field; anywhere else, such as
 * in a plain `z.string()`, they compare it as text.
 */
export function ref<E extends AnyKeyedEntity>(target: E): Ref<E> {
  const schema = (target.fields[target.key] as z.ZodType).clone();
  refTargets.set(schema, target);
  return schema as Ref<E>;
}

/**
 * Returns the schema of a field of an entity's own `fields` whose value is the key of a record of that entity,
 * like SQL's REFERENCES to the same table: `ref(Note)` where `Note` is the entity being defined.
 */
ref.self = (): SelfRef => {
  const schema: z.ZodType = z.lazy(() => {
    const key = selfRefs.get(schema)?.key;
    if (key === undefined) throw new TypeError("ref.self() is only for the fields of entity()");
    return key;
  });
  selfRefs.set(schema, {});
  return schema as SelfRef;
};

export function refTarget(schema: z.ZodType): AnyKeyedEntity | undefined {
  const direct = refTargets.get(schema);
  if (direct !== undefined) return direct;
  if (schema instanceof z.ZodNullable || schema instanceof z.ZodDefault) return refTarget(schema.unwrap() as z.ZodType);
  return undefined;
}

/** Returns the entity whose key a value of `schema` is, as `ref(entity)` or as the entity's key field. */
export function keyTarget(schema: z.ZodType): AnyKeyedEntity | undefined {
  const direct = refTargets.get(schema) ?? keyFieldOwners.get(schema);
  if (direct !== undefined) return direct;
  if (schema instanceof z.ZodNullable || schema instanceof z.ZodDefault) return keyTarget(schema.unwrap() as z.ZodType);
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
