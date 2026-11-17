import type { DefinitionRef } from "./definitionRef.ts";
import type { TransitionRef } from "./transitionRef.ts";

type Of<Kind extends string, Data> = {
  readonly kind: Kind;
  readonly definition: DefinitionRef;
  readonly data: Data;
};

type InTransition = { readonly transition: TransitionRef };

/**
 * A part of a command, query, automation, or chart that some run should reach. A run evaluates bindings and conditions
 * in order and stops at the first null binding or false condition, so `bindsRejection`, `requiresRejection`,
 * `automationBindingNull`, `automationGuard` with `met: false`, and `guardFalse` name only that first one.
 */
export type Obligation =
  | Of<"request", Readonly<Record<string, never>>>
  | Of<"successAnswer", Readonly<Record<string, never>>>
  | Of<"bindsRejection", { readonly binding: string }>
  | Of<"requiresRejection", { readonly condition: string }>
  | Of<"automation", Readonly<Record<string, never>>>
  | Of<"automationBindingValue", { readonly binding: string }>
  | Of<"automationBindingNull", { readonly binding: string }>
  | Of<"automationGuard", { readonly condition: string; readonly met: boolean }>
  | Of<"transition", InTransition>
  | Of<"guardFalse", InTransition & { readonly condition: string }>
  | Of<"state", { readonly state: string }>;

type Unreached<O extends Obligation> = O extends Obligation ? Of<`Uncovered.${O["kind"]}`, O["data"]> : never;

/** The binding that was null or the condition that was false. */
export type Unmet = { readonly binding: string } | { readonly condition: string };

export const rejectedBy = (definition: DefinitionRef, unmet: Unmet): Obligation =>
  "binding" in unmet
    ? { kind: "bindsRejection", definition, data: unmet }
    : { kind: "requiresRejection", definition, data: unmet };

/** A part that neither a scenario's run nor an explored path reached, which test --coverage reports. */
export type Uncovered = Unreached<Obligation>;

export const uncovered = (o: Obligation): Uncovered => ({ ...o, kind: `Uncovered.${o.kind}` }) as Uncovered;
