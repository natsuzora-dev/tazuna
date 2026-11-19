import type { DefinitionRef } from "./definitionRef.ts";
import type { TransitionRef, Trigger } from "./transitionRef.generated.ts";

type Of<Name extends string, Definition extends DefinitionRef | null, Data> = {
  readonly kind: `NonCanonical.${Name}`;
  readonly definition: Definition;
  readonly data: Data;
};

/** The place of the `onRejected` of a state's request: the state, and the trigger of that `onRejected`. */
type OnRejectedAt = { readonly state: string; readonly trigger: Trigger };

/**
 * A form that changes no meaning but is not the one canonical way to write that meaning. `missingOnRejected` and
 * `unreachableOnRejected` name an automation with no data, or the `onRejected` of a state of a machine or screen.
 */
export type NonCanonical =
  /**
   * A keyword written as `{}`, which means what leaving it out means. `path` leads through the keys of the objects
   * written to the definer, and then to `chart()` or `send()`, with array positions as numbers. The definer's `states`
   * holds the states' tree, and `chart()`'s holds their behaviors.
   */
  | Of<"emptyKeyword", DefinitionRef, { readonly path: readonly (string | number)[] }>
  | Of<"emptyKeyword", null, { readonly service: string; readonly path: readonly (string | number)[] }>
  /** A transition to its source state or a descendant of it has no `reenter`. */
  | Of<"missingReenter", DefinitionRef, { readonly transition: TransitionRef }>
  /** A transition of the chart's own `on` has a `reenter`. */
  | Of<"reenterOnRoot", DefinitionRef, { readonly transition: TransitionRef }>
  /** A transition to a state outside its source state has a `reenter`. */
  | Of<"reenterOutsideSource", DefinitionRef, { readonly transition: TransitionRef }>
  /** A literal constant is exported outside a `constants()` call. */
  | Of<"ungroupedConstant", null, { readonly name: string }>
  /** A machine with one state, no context, and nothing to wait for, which turns one event into one command. */
  | Of<"statelessMachine", DefinitionRef, Readonly<Record<string, never>>>
  /** An answer may be rejected, but the request has no `onRejected`. */
  | Of<"missingOnRejected", DefinitionRef, Readonly<Record<string, never>> | OnRejectedAt>
  /** The request has an `onRejected`, but no answer can be rejected. */
  | Of<"unreachableOnRejected", DefinitionRef, Readonly<Record<string, never>> | OnRejectedAt>
  /**
   * An offers entry that returns the same payloads whatever it reads, which a marker writes: `[]` is `none`, and `[{}]`
   * of a control without payload fields is `any`. `state` is null for the chart's own offers.
   */
  | Of<
      "constantOffer",
      DefinitionRef,
      { readonly state: string | null; readonly control: string; readonly marker: "none" | "any" }
    >
  /** An answer written as an object literal, which `accepted`, `fulfilled(output)`, or `rejected(kind, reason)` writes. */
  | Of<"answerLiteral", null, { readonly result: "accepted" | "fulfilled" | "rejected" }>
  /** No function of the command or automation reads the binding of its `binds`. */
  | Of<"unreadBinding", DefinitionRef, { readonly binding: string }>
  | Of<"undescribedService", null, { readonly service: string }>
  | Of<"undescribedDefinition", DefinitionRef, Readonly<Record<string, never>>>;
