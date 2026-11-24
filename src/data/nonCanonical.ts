import type { DefinitionRef } from "./definitionRef.ts";
import type { NonCanonical as StructureNonCanonical } from "./nonCanonical.generated.ts";

type Of<Name extends string, Definition extends DefinitionRef | null, Data> = {
  readonly kind: `NonCanonical.${Name}`;
  readonly definition: Definition;
  readonly data: Data;
};

/** The NonCanonical kinds that only the source shows. */
export type SourceNonCanonical =
  /**
   * A keyword written as `{}`, which means what leaving it out means. `path` leads through the keys of the objects
   * written to the definer, and then to `chart()` or `send()`, with array positions as numbers. The definer's `states`
   * holds the states' tree, and `chart()`'s holds their behaviors.
   */
  | Of<"emptyKeyword", DefinitionRef, { readonly path: readonly (string | number)[] }>
  | Of<"emptyKeyword", null, { readonly service: string; readonly path: readonly (string | number)[] }>
  /** A literal constant is exported outside a `constants()` call. */
  | Of<"ungroupedConstant", null, { readonly name: string }>
  /**
   * An offers entry that returns the same payloads whatever it reads, which a marker writes: `[]` is `none`, and `[{}]`
   * of a control without payload fields is `any`. `state` is null for the chart's own offers.
   */
  | Of<
      "constantOffer",
      DefinitionRef,
      { readonly state: string | null; readonly control: string; readonly marker: "none" | "any" }
    >
  /**
   * An answer to `answered` or to a peer's `answer` written as an object literal, which `accepted()`, `accepted(output)`,
   * `fulfilled(output)`, or `rejected(kind, reason)` writes.
   */
  | Of<"answerLiteral", null, { readonly result: "accepted" | "fulfilled" | "rejected" }>
  /** The service definer `service` has an empty `description`. */
  | Of<"undescribedService", null, { readonly service: string }>
  /** The definition has an empty `description`. */
  | Of<"undescribedDefinition", DefinitionRef, Readonly<Record<string, never>>>;

/**
 * A form that changes no meaning but is not the one canonical way to write that meaning. Lean's Canonical.check finds
 * the kinds that the structure shows, and the checks of src/check/nonCanonical the ones that only the source shows.
 */
export type NonCanonical = StructureNonCanonical | SourceNonCanonical;
