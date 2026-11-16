import type { ChoiceDependent, Difference, StepName } from "../data/choiceDependent.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { type Bindings, renamed } from "../data/trace.ts";
import { byCodePoint, canonicalJson, type Json } from "../data/values.ts";
import type { ViolationValue } from "../data/violation.ts";
import { stepNameDefinition } from "../service/note.ts";
import type { Records } from "../service/records.ts";

/** Lean's stepOrderLimit: the number of step orders that the search of one processing runs at most. */
export const stepOrderLimit = 64;

/** What a run gives the relation: the violation that halted it, the trace lines that verify reads, and its records. */
export interface Outcome {
  readonly halted: ViolationValue | null;
  readonly lines: readonly TraceLine[];
  readonly records: Json;
}

/**
 * Returns the records as the relation compares them: each keyed entity as its encoded rows in key order, and each
 * single entity as its encoded row once it has one.
 */
function recordsValue(records: Records): Json {
  return {
    ...Object.fromEntries(
      [...records.keyed].map(([name, rows]) => [
        name,
        [...rows.keys()].toSorted(byCodePoint).map((key) => rows.get(key)?.encoded),
      ]),
    ),
    ...Object.fromEntries([...records.singles].map(([name, row]) => [name, row.encoded])),
  } as Json;
}

/** Returns what the relation compares of a run: the violation that halted it, or its trace lines and records. */
export function outcomeOf(halted: ViolationValue | null, lines: readonly TraceLine[], records: Records): Outcome {
  if (halted !== null) return { halted, lines: [], records: null };
  return { halted: null, lines, records: recordsValue(records) };
}

/**
 * A comparison that returns the first violation that verify finds in `actual`, with `expected` as the snapshot, or else
 * the bindings of the createKey values of `expected` to those of `actual`.
 */
export type Compare = (
  expected: readonly TraceLine[],
  actual: readonly TraceLine[],
) => { readonly mismatch: ViolationValue } | { readonly bindings: Bindings };

/**
 * Returns the text of records as the relation compares them, with each string that `bindings` binds replaced by its
 * first bound value, and each keyed entity's rows in the order of their texts, since the replaced keys no longer give
 * their order.
 */
function recordsText(bindings: Bindings, records: Json): string {
  const value = renamed(bindings, records);
  if (value === null || typeof value !== "object" || Array.isArray(value)) return canonicalJson(value);
  return canonicalJson(
    Object.fromEntries(
      Object.entries(value).map(([entity, rows]) => [
        entity,
        Array.isArray(rows) ? rows.map(canonicalJson).toSorted(byCodePoint) : rows,
      ]),
    ),
  );
}

type Of<K extends ChoiceDependent["kind"]> = Extract<ChoiceDependent, { readonly kind: K }>;

/** Returns the identity of a halting violation; two halting violations differ when their kinds or data differ. */
const haltIdentity = (v: ViolationValue | null): string | null => (v === null ? null : canonicalJson([v.kind, v.data]));

/**
 * Returns the first difference: the halting violations, then the outputs as `compare` finds them with `original` as the
 * snapshot, then the records, which later inputs read, with the createKey values of `original` replaced by the values
 * of `alternative` that the outputs bind them to.
 */
function difference(compare: Compare, original: Outcome, alternative: Outcome): Difference | undefined {
  if (original.halted !== null || alternative.halted !== null)
    return haltIdentity(original.halted) === haltIdentity(alternative.halted)
      ? undefined
      : { aspect: "halt", original: original.halted, alternative: alternative.halted };
  const compared = compare(original.lines, alternative.lines);
  if ("mismatch" in compared) return { aspect: "outputs", mismatch: compared.mismatch };
  return recordsText(compared.bindings, original.records) === recordsText(new Map(), alternative.records)
    ? undefined
    : { aspect: "records", original: original.records, alternative: alternative.records };
}

/**
 * Lean's stepOrder: the violation when the two walks differ. `aFirst` takes step `a` first and is the walk with the step
 * order `aOrder`, and `bFirst` takes `b` first and is the walk with `bOrder`. The pair is in the order of their canonical
 * texts.
 */
export function stepOrder(
  compare: Compare,
  a: StepName,
  b: StepName,
  aOrder: readonly StepName[],
  bOrder: readonly StepName[],
  aFirst: Outcome,
  bFirst: Outcome,
): Of<"ChoiceDependent.stepOrder"> | undefined {
  const [first, second, originalOrder, alternativeOrder, original, alternative] =
    byCodePoint(canonicalJson(a), canonicalJson(b)) <= 0
      ? [a, b, aOrder, bOrder, aFirst, bFirst]
      : [b, a, bOrder, aOrder, bFirst, aFirst];
  const found = difference(compare, original, alternative);
  return found === undefined
    ? undefined
    : {
        kind: "ChoiceDependent.stepOrder",
        definition: stepNameDefinition(first),
        data: { firstStep: first, secondStep: second, originalOrder, alternativeOrder, difference: found },
      };
}
