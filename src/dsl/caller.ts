import type { AnyKeyedEntity, Entities } from "./entity.ts";

/** The keyed entities of `Es`. */
type KeyedIn<Es extends Entities> = { [K in keyof Es]: Es[K] extends AnyKeyedEntity ? Es[K] : never }[keyof Es];

/** The name under which `Es` lists the entity `E`. */
type NameIn<Es extends Entities, E> = {
  [K in keyof Es & string]: [Es[K]] extends [E] ? ([E] extends [Es[K]] ? K : never) : never;
}[keyof Es & string];

/**
 * A kind of caller that a command or query of a service with the entities `Es` takes: a keyed entity of the service,
 * whose records call, or another service by name. Who is who is decided outside the spec (authentication), as a Cedar
 * request names its principal.
 */
export type CallerType<Es extends Entities = Entities> = KeyedIn<Es> | string;

/**
 * The caller that a function reads as `caller`, of a command or query that lists `Cl`: `{ entity, key }` for a record of
 * an entity, by its key as text, `{ service }` for a service. The fields of the other kind are absent, so that comparing
 * `entity` or `service` tells the kinds apart.
 */
export type CallerOf<Cl, Es extends Entities> = Cl extends readonly (infer T)[]
  ? T extends string
    ? { readonly service: T; readonly entity?: never; readonly key?: never }
    : T extends AnyKeyedEntity
      ? { readonly entity: NameIn<Es, T>; readonly key: string; readonly service?: never }
      : never
  : never;
