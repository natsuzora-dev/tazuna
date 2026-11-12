import { haltingFaultKinds } from "../data/fault.generated.ts";
import { haltingInvalidInputKinds } from "../data/invalidInput.generated.ts";
import type { RejectionKind } from "../data/trace.generated.ts";
import type { Fields } from "../data/values.ts";
import type { Kind } from "../data/violation.ts";

/** Lean's RejectionKind.byCaller. */
export const byCallerKinds: ReadonlySet<RejectionKind> = new Set([
  "invalid-input",
  "reused-id",
  "not-found",
  "requires",
  "already-exists",
]);

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
