import type { ServiceDefinition } from "./definition.ts";
import type { AnyKeyedEntity, Entities } from "./entity.ts";

/** The names of the keyed entities of `Es`. */
type KeyedNames<Es extends Entities> = { [E in keyof Es]: Es[E] extends AnyKeyedEntity ? E : never }[keyof Es];

/** The bounds of the states that `prove` checks the service's invariants in. */
export interface BoundsOptions<Es extends Entities> {
  /** The most records of each keyed entity that the service creates, keys never reused. */
  readonly creates: { readonly [E in KeyedNames<Es>]: number };
}

export type BoundsDefiner<Es extends Entities> = (options: BoundsOptions<Es>) => BoundsOptions<Es>;

const boundsOwners = new WeakMap<object, ServiceDefinition>();

export const boundsDefiner =
  (owner: ServiceDefinition) =>
  (options: BoundsOptions<Entities>): BoundsOptions<Entities> => {
    const creates: Readonly<Record<string, number>> = options.creates;
    for (const [entity, n] of Object.entries(creates))
      if (!Number.isInteger(n) || n < 0)
        throw new RangeError(`bounds() of ${owner.name}: creates.${entity} ${n} is not a non-negative integer`);
    const defined = Object.freeze({ creates: Object.freeze({ ...creates }) });
    boundsOwners.set(defined, owner);
    return defined;
  };

/** The service of a `bounds()` value, or undefined for any other value. */
export const boundsService = (value: unknown): ServiceDefinition | undefined =>
  typeof value === "object" && value !== null ? boundsOwners.get(value) : undefined;
