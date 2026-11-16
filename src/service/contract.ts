import type { Fault } from "../data/fault.generated.ts";
import type { Rejection } from "../data/trace.generated.ts";
import type { Unmet } from "../data/uncovered.ts";
import type { Fields } from "../data/values.ts";
import type { Located } from "../data/violation.ts";
import { ref, requirementsOf } from "./basic.ts";
import { Failed, issueViolation } from "./functions.ts";
import type { RecordSource } from "./records.ts";
import { failedEnsures, halt, type Run } from "./state.ts";

export function firstFalse(
  test: (name: string) => boolean | Failed,
  names: readonly string[],
): string | undefined | Failed {
  for (const name of names) {
    const holds = test(name);
    if (holds instanceof Failed) return holds;
    if (!holds) return name;
  }
  return undefined;
}

/**
 * Returns the reason that the command `name` rejects its input before processing: a ref target that is missing, a binds
 * value that is null, or a requires condition that is false, with what was unmet.
 */
export function requirementsRejection(
  r: Run,
  name: string,
  input: Fields,
  records: RecordSource,
): { readonly rejection: Rejection; readonly unmet?: Unmet } | undefined {
  const rq = requirementsOf(r.st, name);
  for (const [field, target] of rq.refs) {
    const value = input[field];
    if (value === null || value === undefined) continue;
    if (
      target.service === r.st.service &&
      r.st.entities.includes(target.name) &&
      !records.exists(target.name, String(value))
    )
      return { rejection: { kind: "not-found" } };
  }
  const definition = ref(r.st, name);
  const { now } = r.state;
  const unbound = firstFalse((b) => r.functions.binding(name, b, input, records, now), rq.binds);
  if (unbound instanceof Failed) return halt(issueViolation(definition, unbound));
  if (unbound !== undefined) return { rejection: { kind: "requires", reason: unbound }, unmet: { binding: unbound } };
  const failed = firstFalse((c) => r.functions.requirement(name, c, input, records, now), rq.requires);
  if (failed instanceof Failed) return halt(issueViolation(definition, failed));
  if (failed !== undefined) return { rejection: { kind: "requires", reason: failed }, unmet: { condition: failed } };
  return undefined;
}

/** Returns the violation of the first ensures that the accepted command `name` fails. */
export function commandEnsures(
  r: Run,
  name: string,
  input: Fields,
  before: RecordSource,
  after: RecordSource,
): (Fault & Located)[] {
  const definition = ref(r.st, name);
  const failed = r.functions.ensures(name, input, before, after, r.state.now);
  if (failed instanceof Failed) return [issueViolation(definition, failed)];
  if (failed === undefined) return [];
  return [failedEnsures(definition, failed)];
}
