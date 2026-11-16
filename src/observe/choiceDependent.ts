import type { ChoiceDependent, Difference, StepName } from "../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { DeadlineId, TraceLine } from "../data/trace.generated.ts";
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
 * Moves the lines at `positions` together to the earliest of them, so that both orders of two swapped inputs emit their
 * outputs after both inputs, as verify reads them.
 */
function gathered<T>(lines: readonly T[], positions: readonly number[]): T[] {
  const rest = lines.filter((_, i) => !positions.includes(i));
  rest.splice(Math.min(...positions), 0, ...positions.flatMap((i) => (i < lines.length ? [lines[i] as T] : [])));
  return rest;
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

/**
 * Returns what the relation compares of a run: the violation that halted it, or its trace lines, with the lines at
 * `swapped` gathered, and its records.
 */
export function outcomeOf(
  halted: ViolationValue | null,
  lines: readonly TraceLine[],
  records: Records,
  swapped?: readonly number[],
): Outcome {
  if (halted !== null) return { halted, lines: [], records: null };
  return {
    halted: null,
    lines: swapped === undefined ? lines : gathered(lines, swapped),
    records: recordsValue(records),
  };
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
 * Returns the violation when the two deadline orders differ. `aFirst` fires `a` first, and `bFirst` fires `b` first;
 * `chart` gives the chart of a deadline's instance.
 * The pair is in the order of their canonical texts.
 */
export function deadlineOrder(
  compare: Compare,
  chart: (deadline: DeadlineId) => DefinitionRef | null,
  a: DeadlineId,
  b: DeadlineId,
  aFirst: Outcome,
  bFirst: Outcome,
): Of<"ChoiceDependent.deadlineOrder"> | undefined {
  const [first, second, original, alternative] =
    byCodePoint(canonicalJson(a), canonicalJson(b)) <= 0 ? [a, b, aFirst, bFirst] : [b, a, bFirst, aFirst];
  const found = difference(compare, original, alternative);
  return found === undefined
    ? undefined
    : {
        kind: "ChoiceDependent.deadlineOrder",
        definition: chart(first),
        data: { firstDeadline: first, secondDeadline: second, difference: found },
      };
}

/**
 * Returns the violation when the two answer targets differ in outcome. `answered` gives the answer from `sender` to
 * `request`, and `alternative` gives it to `other`.
 */
export function answerChoice(
  compare: Compare,
  sender: DefinitionRef,
  request: string,
  other: string,
  answered: Outcome,
  alternative: Outcome,
): Of<"ChoiceDependent.answerChoice"> | undefined {
  const found = difference(compare, answered, alternative);
  return found === undefined
    ? undefined
    : {
        kind: "ChoiceDependent.answerChoice",
        definition: sender,
        data: { requestId: request, otherRequestId: other, difference: found },
      };
}

/**
 * Returns the violation when the two answer orders differ. `xFirst` answers request `x` from `xSender` first, and
 * `yFirst` answers `y` from `ySender` first. The pair is in the order of the ids.
 */
export function answerOrder(
  compare: Compare,
  x: string,
  y: string,
  xSender: DefinitionRef,
  ySender: DefinitionRef,
  xFirst: Outcome,
  yFirst: Outcome,
): Of<"ChoiceDependent.answerOrder"> | undefined {
  const [first, second, sender, original, alternative] =
    byCodePoint(x, y) <= 0 ? [x, y, xSender, xFirst, yFirst] : [y, x, ySender, yFirst, xFirst];
  const found = difference(compare, original, alternative);
  return found === undefined
    ? undefined
    : {
        kind: "ChoiceDependent.answerOrder",
        definition: sender,
        data: { firstRequestId: first, secondRequestId: second, difference: found },
      };
}

/**
 * Returns the violation when the two request orders differ. `forward` sends `first` first, as one sender did while the
 * other request waited, and `backward` sends `second` first.
 */
export function requestOrder(
  compare: Compare,
  first: DefinitionRef,
  second: DefinitionRef,
  forward: Outcome,
  backward: Outcome,
): Of<"ChoiceDependent.requestOrder"> | undefined {
  const found = difference(compare, forward, backward);
  return found === undefined
    ? undefined
    : { kind: "ChoiceDependent.requestOrder", definition: first, data: { secondRequest: second, difference: found } };
}

/**
 * Returns the violation when the two step orders differ. `aFirst` takes step `a` first, and `bFirst` takes `b` first.
 * The pair is in the order of their canonical texts.
 */
export function stepOrder(
  compare: Compare,
  a: StepName,
  b: StepName,
  aFirst: Outcome,
  bFirst: Outcome,
): Of<"ChoiceDependent.stepOrder"> | undefined {
  const [first, second, original, alternative] =
    byCodePoint(canonicalJson(a), canonicalJson(b)) <= 0 ? [a, b, aFirst, bFirst] : [b, a, bFirst, aFirst];
  const found = difference(compare, original, alternative);
  return found === undefined
    ? undefined
    : {
        kind: "ChoiceDependent.stepOrder",
        definition: stepNameDefinition(first),
        data: { firstStep: first, secondStep: second, difference: found },
      };
}
