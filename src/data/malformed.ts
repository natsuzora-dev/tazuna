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
 * - `duplicateService`: another service definer, exported in the file `elsewhere`, has the name `name` too; a
 *   service's name, which contracts and scenarios carry as a type, names one service.
 * - `unknownService`: the `constants()` call names `name`, which no service definer has.
 * - `reservedNameCharacter`: the service or scenario name `name` contains `character`, one of the characters that
 *   separate the parts of tazuna's generated names (trace names, created keys, line ids, copy names, snapshot names).
 * - `duplicateName`: `name` also names another definition, scenario, or `constants()` call of the service in the file
 *   `elsewhere`.
 * - `alias`: the definition, scenario, or `constants()` call is already exported as `name`.
 * - `unexportedDefinition` and `opaqueCollection`: `path` leads from the definition, service definer, or
 *   `constants()` call through the keys of its object, with array positions as numbers. A schema inside another schema
 *   has the path of the field that holds it, and a chart holds each state's `held` under `held` by the state's name.
 * - `unparsableTime`: a time of the scenario, Given's start or a clock line's time, is not an ISO datetime with
 *   seconds and an offset, or has a part below a millisecond, so the run cannot read it as an instant in milliseconds.
 *   The report is at the clock line, or at the scenario for Given's start.
 * - `unknownPeer`: Given lists as a peer the own service's contract or no contract (null).
 * - `misnamedPeer`: the scenario's Given lists the contract of `service` under the key `name`; a peer is keyed by its
 *   service name.
 * - `writtenCreatedKey`: the scenario writes, in Given or on a line, `key`, a value in the form of a key that a spec
 *   service creates of `entity` (`<service>/<Entity>-<n>`); a scenario reads a created key through a handle, and a
 *   running peer's answer writes `created()`. The report is at the line, or at the scenario for Given.
 * - `lineAfterWhen`: a line of the scenario was placed after its When returned, through a handle kept for later.
 * - `misusedObserved`: the line `input` of the scenario uses the observed value at the field `path` of a handle in the
 *   way `use` (LoweringViolation's ObservedUse) instead of placing it whole in a value; the value exists only when the
 *   scenario runs.
 * - `inexactDelay`: the delay of the deadline `deadline` of `state` has a date unit, a part below a millisecond, or a
 *   value that Temporal does not read, so the run cannot add it to an instant in milliseconds.
 */
export type Malformed =
  | Of<"missingDefiner", null, { readonly name: string }>
  | Of<"unlistedEntity", null, { readonly name: string }>
  | Of<"listedTwice", null, { readonly name: string; readonly services: readonly string[] }>
  | Of<"listedUnderOtherName", DefinitionRef, { readonly key: string }>
  | Of<"duplicateService", null, { readonly name: string; readonly elsewhere: string }>
  | Of<"unknownService", null, { readonly name: string }>
  | Of<"reservedNameCharacter", null, { readonly name: string; readonly character: string }>
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
  | (Of<"unexportedDefinition", null, { readonly name: string; readonly path: readonly (string | number)[] }> & {
      readonly scenario?: DefinitionRef;
    })
  | Of<"unexportedDefinition", null, { readonly contract: string; readonly key: string }>
  | (Of<"unparsableTime", null, Readonly<Record<string, never>>> & { readonly scenario: DefinitionRef })
  | (Of<"unknownPeer", null, { readonly service: string | null }> & { readonly scenario: DefinitionRef })
  | (Of<"misnamedPeer", null, { readonly name: string; readonly service: string }> & {
      readonly scenario: DefinitionRef;
    })
  | (Of<"writtenCreatedKey", null, { readonly key: string; readonly entity: DefinitionRef }> & {
      readonly scenario: DefinitionRef;
    })
  | (Of<"lineAfterWhen", null, Readonly<Record<string, never>>> & { readonly scenario: DefinitionRef })
  | (Of<"misusedObserved", null, { readonly use: string; readonly path: readonly string[] }> & {
      readonly scenario: DefinitionRef;
    })
  | Of<"inexactDelay", DefinitionRef, { readonly state: string; readonly deadline: string }>;
