import type { DefinitionRef } from "./definitionRef.ts";
import type { Uncovered } from "./uncovered.generated.ts";

export type { Uncovered } from "./uncovered.generated.ts";

/** Lean's Uncovered as a run reaches it (Note.reached): the kind without its group. */
export type Obligation = Uncovered extends infer U
  ? U extends { readonly kind: `Uncovered.${infer K}`; readonly definition: DefinitionRef; readonly data: infer D }
    ? { readonly kind: K; readonly definition: DefinitionRef; readonly data: D }
    : never
  : never;

/** The binding that was null or the condition that was false. */
export type Unmet = { readonly binding: string } | { readonly condition: string };

export const rejectedBy = (definition: DefinitionRef, unmet: Unmet): Obligation =>
  "binding" in unmet
    ? { kind: "bindsRejection", definition, data: unmet }
    : { kind: "requiresRejection", definition, data: unmet };

export const uncovered = (o: Obligation): Uncovered => ({ ...o, kind: `Uncovered.${o.kind}` }) as Uncovered;
