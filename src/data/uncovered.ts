import type { DefinitionRef } from "./definitionRef.ts";
import type { TransitionRef } from "./transitionRef.generated.ts";

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
  /** A request to the command or query. */
  | Of<"request", Readonly<Record<string, never>>>
  /** An answer that accepts or fulfills a request to the command or query. */
  | Of<"successAnswer", Readonly<Record<string, never>>>
  /** A rejection of the request because its binding `binding` is null. */
  | Of<"bindsRejection", { readonly binding: string }>
  /** A rejection of the request because its requires `condition` is false. */
  | Of<"requiresRejection", { readonly condition: string }>
  /** A run of the automation. */
  | Of<"automation", Readonly<Record<string, never>>>
  /** A run of the automation in which its binding `binding` has a value. */
  | Of<"automationBindingValue", { readonly binding: string }>
  /** A run of the automation in which its binding `binding` is null. */
  | Of<"automationBindingNull", { readonly binding: string }>
  /** A run of the automation in which its guard `condition` has the value `met`. */
  | Of<"automationGuard", { readonly condition: string; readonly met: boolean }>
  /** A firing of the chart's transition `transition`. */
  | Of<"transition", InTransition>
  /** An evaluation of the guard `condition` of the chart's transition `transition` that is false. */
  | Of<"guardFalse", InTransition & { readonly condition: string }>
  /** An entry into the chart's state `state`. */
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
