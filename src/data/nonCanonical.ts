import type { DefinitionRef } from "./definitionRef.ts";
import type { TransitionRef } from "./transitionRef.ts";

type Of<Name extends string, Definition extends DefinitionRef | null, Data> = {
  readonly kind: `NonCanonical.${Name}`;
  readonly definition: Definition;
  readonly data: Data;
};

/** The place of the `onRejected` of a state's request: the state, and the keys that lead to it from the state. */
type OnRejectedAt = { readonly state: string; readonly keys: readonly string[] };

/**
 * A form that changes no meaning but is not the one canonical way to write that meaning. `missingOnRejected` and
 * `unreachableOnRejected` name an automation with no data, or the `onRejected` of a state of a machine or screen.
 */
export type NonCanonical =
  | Of<"emptyGuard", DefinitionRef, { readonly transition: TransitionRef }>
  | Of<"emptyAfter", DefinitionRef, { readonly state: string }>
  | Of<"missingReenter", DefinitionRef, { readonly transition: TransitionRef }>
  | Of<"reenterOnRoot", DefinitionRef, { readonly transition: TransitionRef }>
  | Of<"reenterOutsideSource", DefinitionRef, { readonly transition: TransitionRef }>
  | Of<"ungroupedConstant", null, { readonly name: string }>
  | Of<"statelessMachine", DefinitionRef, Readonly<Record<string, never>>>
  | Of<"missingOnRejected", DefinitionRef, Readonly<Record<string, never>> | OnRejectedAt>
  | Of<"unreachableOnRejected", DefinitionRef, Readonly<Record<string, never>> | OnRejectedAt>
  | Of<"unreadBinding", DefinitionRef, { readonly binding: string }>
  | Of<"undescribedService", null, { readonly service: string }>
  | Of<"undescribedDefinition", DefinitionRef, Readonly<Record<string, never>>>;
