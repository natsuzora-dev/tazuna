import {
  anySameness,
  type Binding,
  emptyBinding,
  matchesSameness,
  matchValue,
  type Sameness,
  type Values,
} from "../data/binding.ts";
import { Bag } from "../data/canonical.ts";
import type { Assigned, ChoiceDependent, Difference } from "../data/choiceDependent.generated.ts";
import { bindingLimit } from "../data/limits.generated.ts";
import type { StepName } from "../data/step.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { byCodePoint, canonicalJson, type Json } from "../data/values.ts";
import type { ViolationValue } from "../data/violation.ts";
import { stepNameDefinition } from "../service/note.ts";
import type { Records } from "../service/records.ts";

/**
 * Lean's Outcome: the violation that halted a run, the trace lines that verify reads, its records, and the keys that its
 * running services created, each with its domain.
 */
export interface Outcome {
  readonly halted: ViolationValue | null;
  readonly lines: readonly TraceLine[];
  readonly records: Json;
  readonly created: ReadonlyMap<string, string>;
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
export function outcomeOf(
  halted: ViolationValue | null,
  lines: readonly TraceLine[],
  records: Records,
  created: ReadonlyMap<string, string>,
): Outcome {
  if (halted !== null) return { halted, lines: [], records: null, created: new Map() };
  return { halted: null, lines, records: recordsValue(records), created };
}

/**
 * Lean's Compare: the first violation that verify finds in `actual`, with `expected` as the snapshot, or else the set of
 * bindings. `renamed` refines what verify knows of the values (renaming).
 */
export type Compare = (
  renamed: (v: Values) => Values,
  expected: readonly TraceLine[],
  actual: readonly TraceLine[],
) => { readonly mismatch: ViolationValue } | { readonly set: readonly Binding[] };

/** Lean's Outcome.renaming. */
const renaming =
  (original: Outcome, alternative: Outcome) =>
  (v: Values): Values => ({
    ...v,
    domain: (s) => original.created.get(s) ?? v.domain(s),
    image: (s, t) => {
      const d = original.created.get(s);
      return d === undefined ? v.image(s, t) : alternative.created.get(t) === d;
    },
  });

/** Lean's recordsCValue: each keyed entity's rows as a Bag. */
function recordsCValue(records: Json): unknown {
  if (records === null || typeof records !== "object" || Array.isArray(records)) return records;
  return Object.fromEntries(
    Object.entries(records).map(([entity, rows]) => [entity, Array.isArray(rows) ? new Bag(rows) : rows]),
  );
}

/** Lean's sameRecords. */
function sameRecords(set: readonly Binding[], original: Outcome, alternative: Outcome): Sameness {
  const values = renaming(
    original,
    alternative,
  )({ domain: () => "", fresh: new Set(original.created.keys()), image: () => true });
  const [o, a] = [recordsCValue(original.records), recordsCValue(alternative.records)];
  return anySameness(set.map((b) => matchesSameness(matchValue(values, b, o, a))));
}

type Of<K extends ChoiceDependent["kind"]> = Extract<ChoiceDependent, { readonly kind: K }>;

/** Returns the identity of a halting violation; two halting violations differ when their kinds or data differ. */
const haltIdentity = (v: ViolationValue | null): string | null => (v === null ? null : canonicalJson([v.kind, v.data]));

/** Lean's Comparison: no difference (`undefined`), a difference, or too many renamings to tell. */
type Comparison = Difference | "uncomparable" | undefined;

/** Lean's difference. */
function difference(compare: Compare, original: Outcome, alternative: Outcome): Comparison {
  if (original.halted !== null || alternative.halted !== null)
    return haltIdentity(original.halted) === haltIdentity(alternative.halted)
      ? undefined
      : { aspect: "halt", original: original.halted, alternative: alternative.halted };
  const records = (set: readonly Binding[]): Comparison => {
    const same = sameRecords(set, original, alternative);
    if (same === "same") return undefined;
    if (same === "uncomparable") return same;
    return { aspect: "records", original: original.records, alternative: alternative.records };
  };
  const compared = compare(renaming(original, alternative), original.lines, alternative.lines);
  if (!("mismatch" in compared)) return records(compared.set);
  return "mismatch" in compare(renaming(original, original), original.lines, original.lines)
    ? records([emptyBinding])
    : { aspect: "outputs", mismatch: compared.mismatch };
}

/** Lean's Comparison.violation. */
const uncomparable = (
  definition: Of<"ChoiceDependent.uncomparable">["definition"],
): Of<"ChoiceDependent.uncomparable"> => ({
  kind: "ChoiceDependent.uncomparable",
  definition,
  data: { limit: bindingLimit },
});

/**
 * Lean's stepOrder: the violation when the two executions differ. `aFirst` takes step `a` first and is the execution with the step
 * order `aOrder`, and `bFirst` takes `b` first and is the execution with `bOrder`. The pair is in the order of their canonical
 * texts.
 */
export function stepOrder(
  compare: Compare,
  service: string,
  a: StepName,
  b: StepName,
  aOrder: readonly StepName[],
  bOrder: readonly StepName[],
  aFirst: Outcome,
  bFirst: Outcome,
): Of<"ChoiceDependent.stepOrder" | "ChoiceDependent.uncomparable"> | undefined {
  const [first, second, originalOrder, alternativeOrder, original, alternative] =
    byCodePoint(canonicalJson(a), canonicalJson(b)) <= 0
      ? [a, b, aOrder, bOrder, aFirst, bFirst]
      : [b, a, bOrder, aOrder, bFirst, aFirst];
  const found = difference(compare, original, alternative);
  if (found === "uncomparable") return uncomparable(stepNameDefinition(service, first));
  return found === undefined
    ? undefined
    : {
        kind: "ChoiceDependent.stepOrder",
        definition: stepNameDefinition(service, first),
        data: { firstStep: first, secondStep: second, originalOrder, alternativeOrder, difference: found },
      };
}

/**
 * Lean's assignment: the violation for the assignment `assigned` at the first running service, in the order of
 * `outcomes`, whose outcome differs between the execution with each handle at its own place and the execution with `assigned`.
 */
export function assignment(
  compareFor: (service: string) => Compare,
  definition: Of<"ChoiceDependent.assignment">["definition"],
  assigned: readonly Assigned[],
  outcomes: readonly (readonly [string, Outcome, Outcome])[],
): Of<"ChoiceDependent.assignment" | "ChoiceDependent.uncomparable"> | undefined {
  for (const [service, original, alternative] of outcomes) {
    const found = difference(compareFor(service), original, alternative);
    if (found === "uncomparable") return uncomparable(definition);
    if (found !== undefined)
      return { kind: "ChoiceDependent.assignment", definition, data: { service, assigned, difference: found } };
  }
  return undefined;
}
