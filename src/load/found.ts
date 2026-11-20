import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { InternalError } from "../data/internalError.ts";
import type { Placed, ViolationError, ViolationValue } from "../data/violation.ts";
import { type ReportedViolation, toReported } from "../data/violation.ts";
import type { Definition, Named, Place } from "../dsl/definition.ts";

export interface Found<V> {
  readonly violation: V;
  readonly place: Place;
  readonly error?: ViolationError;
}

export const comparePlaces = (x: Place, y: Place): number =>
  x.file.localeCompare(y.file) || x.line - y.line || x.column - y.column;

export const reportedOfFound = ({ violation, place, error }: Found<ViolationValue & Placed>): ReportedViolation =>
  toReported({ ...violation, ...(error === undefined ? {} : { error }) }, place);

export function placeOf(
  spec: { readonly definitions: readonly Named<Definition>[] },
  definition: DefinitionRef | null,
): Place {
  const found = spec.definitions.find((d) => sameRef(d, definition));
  if (found === undefined) throw new InternalError(`no definition ${definition?.service}.${definition?.name}`);
  return found.place;
}
