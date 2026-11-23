import { z } from "zod";
import type { Bag, Made, MarkOf, Runs } from "../data/bag.ts";
import { childrenOf, schemaNode } from "../data/schemaNode.ts";
import type { DateLabel } from "../data/time.ts";
import type { Shape } from "../data/values.ts";
import type { Conditions, Named, Now } from "./conditions.ts";

export type DefaultedShape = Readonly<Record<string, z.ZodDefault<z.ZodType>>>;
/** The type T with every nested object and array readonly, each bag and set a Bag, and each sortedBy array Runs. */
export type Immutable<T> = T extends DateLabel
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

/** A record's values as expressions receive them. Changing one is a type error. */
export type Row<S extends Shape> = Immutable<z.output<z.ZodObject<{ -readonly [K in keyof S]: S[K] }>>>;
/** Values of shape `S` as expressions return them: a bag, set or sortedBy field also takes a Bag. */
export type MadeRow<S extends Shape> = Made<Row<S>>;

/**
 * A bounded response: once `when` holds of a record and `expect` does not, `expect` must hold of it within `within`
 * milliseconds (`Fault.missedResponse`).
 */
export interface Response<Args> {
  readonly when: (args: Args) => boolean;
  readonly expect: (args: Args) => boolean;
  /** The milliseconds, a whole number, by which `expect` must hold. */
  readonly within: number;
}

export type Responses<Args> = Readonly<Record<string, Response<Args>>>;

export interface KeyedEntity<S extends Shape = Shape, K extends keyof S & string = keyof S & string> {
  readonly kind: "entity";
  readonly single: false;
  readonly description: string;
  readonly fields: S;
  readonly key: K;
  readonly unique: readonly (keyof S & string)[];
  readonly invariants: Conditions<{ record: Row<S> } & Now>;
  readonly responses: Responses<{ record: Row<S> } & Now>;
}

export interface SingleEntity<S extends Shape = Shape> {
  readonly kind: "entity";
  readonly single: true;
  readonly description: string;
  readonly fields: S;
  readonly invariants: Conditions<{ record: Row<S> } & Now>;
  readonly responses: Responses<{ record: Row<S> } & Now>;
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
/** The `ref.self()` placeholders. `entity()` claims one by setting its refTargets entry to the entity. */
const selfRefs = new WeakSet<z.ZodType>();

declare const selfMark: unique symbol;
type SelfRef = z.ZodType<unknown, unknown> & { readonly [selfMark]: true };
/**
 * `T` with each `ref.self()` in it, alone or under nullable, optional, default, array or object, as the key schema
 * `Key`. Under a union it types as `unknown`, though its value is still a key at runtime.
 */
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
          : T extends z.ZodObject<infer O extends Shape, infer C>
            ? z.ZodObject<{ -readonly [F in keyof O]: Resolved<O[F], Key> }, C>
            : T;
type SelfResolved<S extends Shape, K extends keyof S> = { [F in keyof S]: Resolved<S[F], S[K]> };

/** Returns the unclaimed `ref.self()` placeholders in `schema`. */
function unclaimedSelfRefs(schema: z.ZodType, seen = new Set<z.ZodType>()): z.ZodType[] {
  if (seen.has(schema)) return [];
  seen.add(schema);
  if (selfRefs.has(schema)) return refTargets.has(schema) ? [] : [schema];
  return childrenOf(schemaNode(schema)).flatMap((child) => unclaimedSelfRefs(child, seen));
}

/**
 * Defines the shape of records identified by `key`. Other definitions reuse a field's schema as `Task.fields.title`.
 */
export function entity<
  const S extends Shape,
  const K extends keyof S & string,
  const Iv extends string = never,
  const Rs extends string = never,
>(definition: {
  description: string;
  /** A field that can be null is `.nullable()`. A field that holds the key of a record of this entity is `ref.self()`. */
  fields: S;
  /** The key field, whose value never changes after the record is created. */
  key: K;
  /** The fields whose combined values no two records share. A record with null in any of them is not checked. */
  unique?: readonly (keyof S & string)[];
  /** The conditions that every record meets (`Fault.failedEntityInvariant`). */
  invariants?: Named<Iv, { record: Row<SelfResolved<S, K>> } & Now>;
  /** The bounded responses of each record (`Fault.missedResponse`). */
  responses?: { readonly [N in Rs]: Response<{ record: Row<SelfResolved<S, K>> } & Now> };
}): KeyedEntity<SelfResolved<S, K>, K> {
  // A clone, so that a schema that the key field shares with other fields does not mark them as key positions too.
  const shared = definition.fields[definition.key] as z.ZodType;
  if (selfRefs.has(shared)) throw new TypeError("the key field of an entity cannot be ref.self()");
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
    invariants: (definition.invariants ?? {}) as Conditions<{ record: Row<SelfResolved<S, K>> } & Now>,
    responses: (definition.responses ?? {}) as Responses<{ record: Row<SelfResolved<S, K>> } & Now>,
  };
  keyFieldOwners.set(key, keyed);
  for (const field of Object.values(definition.fields) as z.ZodType[])
    for (const self of unclaimedSelfRefs(field)) refTargets.set(self, keyed);
  return keyed;
}

/** Defines an entity with exactly one record. `records.Settings` is that record. */
export function singleEntity<
  const S extends DefaultedShape,
  const Iv extends string = never,
  const Rs extends string = never,
>(definition: {
  description: string;
  fields: S;
  /** The conditions that the record meets (`Fault.failedSingleInvariant`). */
  invariants?: Named<Iv, { record: Row<S> } & Now>;
  /** The bounded responses of the record (`Fault.missedResponse`). */
  responses?: { readonly [N in Rs]: Response<{ record: Row<S> } & Now> };
}): SingleEntity<S> {
  return {
    kind: "entity",
    single: true,
    description: definition.description,
    fields: definition.fields,
    invariants: (definition.invariants ?? {}) as Conditions<{ record: Row<S> } & Now>,
    responses: (definition.responses ?? {}) as Responses<{ record: Row<S> } & Now>,
  };
}

declare const refEntity: unique symbol;

export type Ref<E extends AnyKeyedEntity> = z.ZodType<KeyValue<E>, KeyValue<E>> & { readonly [refEntity]: E };

/**
 * Returns the schema of a field whose value is the key of a `target` record. `test` and `verify` compare a created key
 * through the binding only where its schema is `ref(target)`, `ref.self()` in `target`'s own fields, or `target`'s key
 * field. Anywhere else, such as in a plain `z.string()`, they compare it as text.
 *
 * A command of `target`'s service rejects an input with `not-found`, before it checks binds and requires, when a
 * top-level `ref(target)` field of the input names a key that no `target` record has.
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
  // One outside the fields of entity() reads no value until load reports it (Malformed.misplacedSelfRef).
  const schema: z.ZodType = z.lazy(() => {
    const owner = refTargets.get(schema);
    return owner === undefined ? z.never() : (owner.fields[owner.key] as z.ZodType);
  });
  selfRefs.add(schema);
  return schema as SelfRef;
};

/** Whether `schema` is a `ref.self()`, a z.lazy that reads its entity's key field once the entity is defined. */
export const isSelfRef = (schema: z.ZodType): boolean => selfRefs.has(schema);

/** Whether `schema` is a `ref.self()` that no `entity()` claimed, as one outside the fields of an entity is. */
export const misplacedSelfRef = (schema: z.ZodType): boolean => selfRefs.has(schema) && !refTargets.has(schema);

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

/** A table per keyed entity. The record itself per single entity. */
export type Records<Es extends Entities> = {
  readonly [N in keyof Es]: Es[N] extends AnyKeyedEntity
    ? Table<Es[N]>
    : Es[N] extends SingleEntity<infer S>
      ? Row<S>
      : never;
};
