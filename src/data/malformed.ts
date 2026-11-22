import type { DefinitionRef } from "./definitionRef.ts";
import type { UnrepresentableType } from "./jsonSchema.ts";
import type { Collection } from "./marks.ts";

/** What a reference must name: a definition of that kind, or a keyed entity. */
export type Expected = "keyedEntity" | "entity" | "event" | "command" | "query" | "screen";

type Of<Name extends string, Definition extends DefinitionRef | null, Data> = {
  readonly kind: `Malformed.${Name}`;
  readonly definition: Definition;
  readonly data: Data;
};

/**
 * A spec that the loader cannot read faithfully, or whose declared defaults fail their own schemas or throw. When the
 * loader finds one, check skips the structure checks (`Illegal`).
 *
 * `path` leads from the definition, service definer, or `constants()` call through the keys of its object, with array
 * positions as numbers. A schema inside another schema has the path of the field that holds it.
 */
export type Malformed =
  /**
   * The program of `tsconfig`, the nearest tsconfig.json, does not include the spec file, so tsc did not check it
   * (TypeScript's TS6307).
   */
  | Of<"unlistedFile", null, { readonly tsconfig: string }>
  /** The service definer that the definition names is not exported. */
  | Of<"missingDefiner", null, { readonly name: string }>
  /** The exported entity `name` is listed by no service definer. */
  | Of<"unlistedEntity", null, { readonly name: string }>
  /** The entity `name` is listed by more than one service definer, those of `services`. */
  | Of<"listedTwice", null, { readonly name: string; readonly services: readonly string[] }>
  /** A service definer lists the entity under `key`, not under its export name, which also names its records. */
  | Of<"listedUnderOtherName", DefinitionRef, { readonly key: string }>
  /**
   * Another service definer, exported in the file `elsewhere`, has the name `name` too. A service's name, which
   * contracts and scenarios carry as a type, names one service.
   */
  | Of<"duplicateService", null, { readonly name: string; readonly elsewhere: string }>
  /** The `constants()` or `explore()` call names `name`, which no service definer has. */
  | Of<"unknownService", null, { readonly name: string }>
  /** The service `service` has scenarios and no `explore()`, which bounds the paths that `test` explores after them. */
  | Of<"missingExplore", null, { readonly service: string }>
  /** Another `explore()` call names the service `service` too. */
  | Of<"duplicateExplore", null, { readonly service: string }>
  /**
   * The value at index `value` of the domain at index `domain` of the `explore()` of `service` is not JSON, which a
   * scenario line writes, or the domain's schema rejects it, refinements included.
   */
  | Of<"domainValue", null, { readonly service: string; readonly domain: number; readonly value: number }>
  /**
   * The domain at index `domain` of the `explore()` of `service` names no node of a schema that the service's moves may
   * carry: its schema is written nowhere there, or only inside an array or a record.
   */
  | Of<"unusedDomain", null, { readonly service: string; readonly domain: number }>
  /**
   * The domains at the indices `domains` of the `explore()` of `service` cover one node: they name it, or one names it
   * and another names a node around it, whose values explore writes whole. Which values the node takes would depend on
   * which domain is read.
   */
  | Of<"overlappingDomain", null, { readonly service: string; readonly domains: readonly number[] }>
  /**
   * The service or scenario name `name` contains `character`, one of the characters that separate the parts of tazuna's
   * generated names (trace names, created keys, line ids, copy names, snapshot names).
   */
  | Of<"reservedNameCharacter", null, { readonly name: string; readonly character: string }>
  /**
   * The service name, or the scenario name within its service, differs from `collidesWith` only in case or Unicode
   * normalization, so their snapshot and trace files are one file on a case-insensitive file system.
   */
  | Of<"caseCollision", null, { readonly name: string; readonly collidesWith: string }>
  /** `name` also names another definition, scenario, or `constants()` call of the service in the file `elsewhere`. */
  | Of<"duplicateName", null, { readonly name: string; readonly elsewhere: string }>
  /** The definition, scenario, or `constants()` call is already exported as `name`. */
  | Of<"alias", null, { readonly name: string; readonly alias: string }>
  /**
   * A `bag`, `set`, or sorted collection is inside a schema at `path` that tazuna does not look into, such as a
   * `z.record`, so tazuna cannot write its values in canonical order.
   */
  | Of<"opaqueCollection", DefinitionRef, { readonly path: readonly string[]; readonly collection: Collection["kind"] }>
  | Of<
      "opaqueCollection",
      null,
      { readonly name: string; readonly path: readonly string[]; readonly collection: Collection["kind"] }
    >
  /**
   * The schema at `path` has a value that tazuna cannot write back as JSON, of the Zod type `type`: one that JSON
   * cannot hold, such as `bigint` or `set`, or an `intersection`, whose JSON Schema cannot reject a field that neither
   * side names, so objects are joined with `.extend()`. A `getter` is an object that names itself in a getter of its
   * shape, which tazuna cannot walk to its end; an entity whose rows ref() each other holds such data.
   */
  | Of<"unrepresentableSchema", DefinitionRef, { readonly path: readonly string[]; readonly type: UnrepresentableType }>
  | Of<
      "unrepresentableSchema",
      null,
      { readonly name: string; readonly path: readonly string[]; readonly type: UnrepresentableType }
    >
  /** A `ref.self()` at `path` is outside the fields of `entity()`, where no entity's key gives it a schema. */
  | Of<"misplacedSelfRef", DefinitionRef, { readonly path: readonly string[] }>
  | Of<"misplacedSelfRef", null, { readonly name: string; readonly path: readonly string[] }>
  /**
   * A declared default fails its own schema or throws: a single entity's fields, the copy context of the map state
   * `map`, or a schema whose conversion throws.
   */
  | Of<"defaultSchema", DefinitionRef, Readonly<Record<string, never>>>
  | Of<"defaultSchema", DefinitionRef, { readonly map: string }>
  /**
   * The definition, service definer, `constants()` call, or contract refers at `path` to a definition object that no
   * export of the spec names.
   */
  | Of<"unexportedDefinition", DefinitionRef, { readonly path: readonly (string | number)[] }>
  | Of<"unexportedDefinition", null, { readonly service: string; readonly path: readonly (string | number)[] }>
  | (Of<"unexportedDefinition", null, { readonly name: string; readonly path: readonly (string | number)[] }> & {
      readonly scenario?: DefinitionRef;
    })
  | Of<"unexportedDefinition", null, { readonly contract: string; readonly key: string }>
  /**
   * The definition names at `path` no definition of the kind `expected`, or no keyed entity: the entry is missing, there
   * is more than one in an automation's `receives` or `commands`, or it names a definition of another kind. Only a value
   * of type `any` gets any of them past the types.
   */
  | Of<
      "unresolvedReference",
      DefinitionRef,
      { readonly path: readonly (string | number)[]; readonly expected: Expected }
    >
  /**
   * The deadline at `path` writes both a delay and `at`, or neither, so it has no one time. Only a value of type `any`
   * gets it past the types.
   */
  | Of<"unreadableDeadline", DefinitionRef, { readonly path: readonly (string | number)[] }>
  /**
   * A time of the scenario, Given's start or a clock line's time, is no safe integer, so the run cannot hold it as an
   * instant in milliseconds. The report is at the clock line, or at the scenario for Given's start.
   */
  | (Of<"inexactTime", null, Readonly<Record<string, never>>> & { readonly scenario: DefinitionRef })
  /** Given lists as a peer the own service's contract or no contract (null). */
  | (Of<"unknownPeer", null, { readonly service: string | null }> & { readonly scenario: DefinitionRef })
  /**
   * The scenario writes, in Given, on a line, or in an expectation of Then, `key`, a value in the form of a key that a
   * spec service creates of `entity` (`<service>/<Entity>-<n>`). A scenario reads a created key through a handle, and a
   * running peer's answer writes `created()`. The report is at the line or the expectation, or at the scenario for Given.
   */
  | (Of<"writtenCreatedKey", null, { readonly key: string; readonly entity: DefinitionRef }> & {
      readonly scenario: DefinitionRef;
    })
  /** A line of the scenario was placed after its When returned, through a handle kept for later. */
  | (Of<"lineAfterWhen", null, Readonly<Record<string, never>>> & { readonly scenario: DefinitionRef })
  /**
   * The line `input` of the scenario uses the observed value at the field `path` of a handle in the way `use`
   * (LoweringViolation's ObservedUse) instead of placing it whole in a value. The value exists only when the scenario
   * runs.
   */
  | (Of<"misusedObserved", null, { readonly use: string; readonly path: readonly string[] }> & {
      readonly scenario: DefinitionRef;
    });
