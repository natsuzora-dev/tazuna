import type { z } from "zod";
import type { Made } from "../data/bag.ts";
import { bagged, sorted } from "../data/collections.ts";
import { objectOf, type Shape } from "../data/values.ts";
import type {
  AnyEvent,
  CreateEvent,
  DeleteEvent,
  Emit,
  FieldsEvent,
  Owned,
  Payload,
  ServiceDefinition,
  UpdateEvent,
} from "./definition.ts";
import type { AnyEntity, AnyKeyedEntity, Entities, KeyedEntity, SingleEntity } from "./entity.ts";
import { withWritten } from "./written.ts";

type WritableField<E extends AnyEntity> =
  E extends KeyedEntity<infer S, infer K>
    ? Exclude<keyof S & string, K>
    : E extends SingleEntity<infer S>
      ? keyof S & string
      : never;

type KeyedIn<Es extends Entities> = Extract<Es[keyof Es], AnyKeyedEntity>;

export type CreateEventDefiner<Es extends Entities, N extends string> = <const E extends KeyedIn<Es>>(definition: {
  entity: E;
}) => CreateEvent<E> & Owned<N>;

export type UpdateEventDefiner<Es extends Entities, N extends string> = <
  const E extends Es[keyof Es],
  const W extends WritableField<E>,
>(definition: {
  entity: E;
  /** The fields that the event writes, never the key. */
  writes: readonly W[];
}) => UpdateEvent<E, W> & Owned<N>;

export type DeleteEventDefiner<Es extends Entities, N extends string> = <const E extends KeyedIn<Es>>(definition: {
  entity: E;
}) => DeleteEvent<E> & Owned<N>;

export type EventDefiner<N extends string> = <const S extends Shape = Record<never, never>>(definition: {
  payload?: S;
}) => FieldsEvent<S> & Owned<N>;

type EventOptions = {
  entity?: AnyEntity;
  writes?: readonly string[];
  payload?: Shape;
};

export function eventDefiners(owner: ServiceDefinition) {
  const of =
    (change: AnyEvent["change"]) =>
    (d: EventOptions): AnyEvent =>
      withWritten(
        {
          kind: "event",
          change,
          service: owner,
          ...(change === "none" ? {} : { entity: d.entity }),
          ...(change === "update" ? { writes: d.writes } : {}),
          payload: payloadOf(change, d),
        } as AnyEvent,
        d,
      );
  return { createEvent: of("create"), updateEvent: of("update"), deleteEvent: of("delete"), event: of("none") };
}

function payloadOf(change: AnyEvent["change"], d: EventOptions): Shape {
  if (change === "none") return d.payload ?? {};
  const entity = d.entity as AnyEntity;
  const fields = entity.fields as Shape;
  const key = entity.single ? [] : [(entity as AnyKeyedEntity).key];
  const keys = change === "create" ? Object.keys(fields) : [...key, ...(change === "update" ? (d.writes ?? []) : [])];
  return Object.fromEntries(keys.map((k: string) => [k, fields[k] as z.ZodType]));
}

export type PayloadShape<Ev extends AnyEvent> =
  Ev extends CreateEvent<KeyedEntity<infer S>>
    ? S
    : Ev extends UpdateEvent<infer E, infer W>
      ? E extends KeyedEntity<infer S, infer K>
        ? Pick<S, K | (W & keyof S)>
        : E extends SingleEntity<infer S>
          ? Pick<S, W & keyof S>
          : never
      : Ev extends DeleteEvent<KeyedEntity<infer S, infer K>>
        ? Pick<S, K>
        : Ev extends FieldsEvent<infer S>
          ? S
          : never;

/** A payload in trace form: datetime and date values are strings, also in nested fields. */
export type EncodedPayload<Ev extends AnyEvent> = z.input<
  z.ZodObject<{ -readonly [K in keyof PayloadShape<Ev>]: PayloadShape<Ev>[K] }>
>;

/** Returns one event for the result of a command's `decide`. Its payload holds each bag and set as a Bag. */
export function emit<const Ev extends AnyEvent>(ev: Ev, payload: Made<Payload<Ev>>): Emit<Ev> {
  const object = objectOf(ev.payload);
  return { kind: "emit", event: ev, payload: bagged(object, sorted(object, payload)) as Payload<Ev> };
}
