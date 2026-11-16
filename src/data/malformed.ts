import type { Collection } from "./collections.ts";
import type { DefinitionRef } from "./definitionRef.ts";

type Of<Name extends string, Definition extends DefinitionRef | null, Data> = {
  readonly kind: `Malformed.${Name}`;
  readonly definition: Definition;
  readonly data: Data;
};

/**
 * A spec that the loader cannot read faithfully, or whose declared defaults fail their own schemas or throw. When the
 * loader finds one, check skips the structure checks (Illegal).
 *
 * - `missingDefiner`: the definer that the definition names is not exported.
 * - `listedUnderOtherName`: a service definer lists the entity under `key`, not under its export name, which also names
 *   its records.
 * - `duplicateName`: `name` also names another definition, scenario, or `constants()` call of the service in the file
 *   `elsewhere`.
 * - `alias`: the definition, scenario, or `constants()` call is already exported as `name`.
 * - `unexportedDefinition` and `opaqueCollection`: `path` leads from the definition, scenario, service definer, or
 *   `constants()` call through the keys of its object, with array positions as numbers. A schema inside another schema
 *   has the path of the field that holds it, and a chart holds each state's `held` under `held` by the state's name.
 * - `unparsableTime`: the time of the `at` input of the scenario, or of the state `state` of the contract of
 *   `contract`, is not an ISO datetime with seconds and an offset, or has a part below a millisecond, so the run cannot
 *   read it as an instant in milliseconds.
 * - `unknownPeer`: the scenario's `given` names `service`, or its `elsewhere` or `from` input names the contract of
 *   `service`, or an object that is no exported contract (null), and `service` is the scenario's own service, an
 *   external service, or no service of the spec.
 * - `unlistedState`: the scenario's `given` gives `service` a start state that is not one of the states of its
 *   contract.
 * - `ownMessageToPeer`: the start state that the scenario's `given` gives `service`, or its `elsewhere` input to
 *   `service`, receives an event of the scenario's own service or answers a request to it, which reach `service` only
 *   from the scenario's run.
 * - `misnamedPeer`: the scenario's Given lists the contract of `service` under the key `name`; a peer is keyed by its
 *   service name.
 * - `unlistedPeer`: the scenario's own service exchanges messages with `service` (its definitions name the other's), and
 *   Given does not list it as run, external, or skip.
 * - `invalidRecord`: the scenario's Given writes a record of `entity` of `service` that is no entity of that service,
 *   that has no string `key`, or that does not match the entity's schema.
 * - `lineAfterWhen`: a line of the scenario was placed after its When returned, through a handle kept for later.
 * - `inexactDelay`: the delay of the deadline `deadline` of `state` has a date unit, a part below a millisecond, or a
 *   value that Temporal does not read, so the run cannot add it to an instant in milliseconds.
 */
export type Malformed =
  | Of<"missingDefiner", null, { readonly name: string }>
  | Of<"unlistedEntity", null, { readonly name: string }>
  | Of<"listedTwice", null, { readonly name: string; readonly services: readonly string[] }>
  | Of<"listedUnderOtherName", DefinitionRef, { readonly key: string }>
  | Of<"serviceInSharedFolder", null, { readonly folder: string }>
  | Of<"splitService", null, { readonly folder: string; readonly elsewhere: string }>
  | Of<"duplicateName", null, { readonly name: string; readonly elsewhere: string }>
  | Of<"alias", null, { readonly name: string; readonly alias: string }>
  | Of<"opaqueCollection", DefinitionRef, { readonly path: readonly string[]; readonly collection: Collection["kind"] }>
  | Of<
      "opaqueCollection",
      null,
      { readonly name: string; readonly path: readonly string[]; readonly collection: Collection["kind"] }
    >
  | Of<"defaultSchema", DefinitionRef, Readonly<Record<string, never>>>
  | Of<"defaultSchema", DefinitionRef, { readonly map: string }>
  | Of<"unexportedDefinition", DefinitionRef, { readonly path: readonly (string | number)[] }>
  | Of<"unexportedDefinition", null, { readonly service: string; readonly path: readonly (string | number)[] }>
  | Of<"unexportedDefinition", null, { readonly name: string; readonly path: readonly (string | number)[] }>
  | Of<"unexportedDefinition", null, { readonly contract: string; readonly key: string }>
  | (Of<"unparsableTime", null, Readonly<Record<string, never>>> & {
      readonly scenario: DefinitionRef;
      readonly input: number;
    })
  | (Of<"unparsableTime", null, { readonly contract: string; readonly state: string }> & { readonly input: number })
  | (Of<"unknownPeer", null, { readonly service: string | null }> & {
      readonly scenario: DefinitionRef;
      readonly input?: number;
    })
  | (Of<"unlistedState", null, { readonly service: string }> & { readonly scenario: DefinitionRef })
  | (Of<"ownMessageToPeer", null, { readonly service: string }> & {
      readonly scenario: DefinitionRef;
      readonly input?: number;
    })
  | (Of<"misnamedPeer", null, { readonly name: string; readonly service: string }> & {
      readonly scenario: DefinitionRef;
    })
  | (Of<"unlistedPeer", null, { readonly service: string }> & { readonly scenario: DefinitionRef })
  | (Of<"invalidRecord", null, { readonly service: string; readonly entity: string; readonly key?: string }> & {
      readonly scenario: DefinitionRef;
    })
  | (Of<"lineAfterWhen", null, Readonly<Record<string, never>>> & { readonly scenario: DefinitionRef })
  | Of<"inexactDelay", DefinitionRef, { readonly state: string; readonly deadline: string }>;
