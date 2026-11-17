import { haltingFaultKinds } from "../data/fault.generated.ts";
import { haltingInvalidInputKinds } from "../data/invalidInput.generated.ts";
import { byCallerKinds, type RejectionKind } from "../data/trace.generated.ts";
import type { Fields, Json } from "../data/values.ts";
import type { Kind } from "../data/violation.ts";

/** Lean's RejectionKind.byCaller. */
export const byCaller: ReadonlySet<RejectionKind> = new Set(byCallerKinds);

/** The kinds whose violations halt the run. */
export type Halting = (typeof haltingFaultKinds)[number] | (typeof haltingInvalidInputKinds)[number];

const halting: ReadonlySet<Kind> = new Set<Kind>([...haltingFaultKinds, ...haltingInvalidInputKinds]);

/** Lean's Finding.halts. */
export const halts = (kind: Kind): boolean => halting.has(kind);

/** An emitted event. `event` is its trace name as seen from the service, and `payload` is decoded. */
export interface Emit {
  readonly event: string;
  readonly payload: Fields;
}

/** An emitted event that a service took, with `encoded`, the payload as Lean's Emit holds it, which names its steps. */
export interface Emitted extends Emit {
  readonly encoded: Json;
}
