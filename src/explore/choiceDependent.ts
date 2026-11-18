import {
  anySameness,
  type Binding,
  emptyBinding,
  matchesSameness,
  matchValue,
  type Sameness,
  type Values,
} from "../data/binding.ts";
import { Bag, Ref } from "../data/canonical.ts";
import type { ChoiceDependent, Difference } from "../data/choiceDependent.generated.ts";
import { bindingLimit } from "../data/limits.generated.ts";
import type { StepName } from "../data/step.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { byCodePoint, canonicalJson, type Fields, plain } from "../data/values.ts";
import type { ViolationValue } from "../data/violation.ts";
import { ref, type Service } from "../service/basic.ts";
import { stepNameDefinition } from "../service/note.ts";
import type { Records } from "../service/records.ts";

/**
 * Lean's Outcome: the violation that halted a run, the trace lines that verify reads, its records (recordsValue), and
 * the keys that its running services created, each with its domain.
 */
export interface Outcome {
  readonly halted: ViolationValue | null;
  readonly lines: readonly TraceLine[];
  readonly records: unknown;
  readonly created: ReadonlyMap<string, string>;
}

/** Lean's keyFields: entity `e`'s key field and ref() fields, each with the domain of the entity it names. */
function keyFields(st: Service, e: string): ReadonlyMap<string, string> {
  const found = st.structure.definitions.find((d) => d.kind === "entity" && d.service === st.service && d.name === e);
  if (found?.kind !== "entity") return new Map();
  const domain = ({ service, name }: { service: string; name: string }) => `${service}/${name}`;
  return new Map([
    ...(found.key === null ? [] : [[found.key, domain(ref(st, e))] as const]),
    ...found.references.flatMap((r) => (r.entity === null ? [] : [[r.field, domain(r.entity)] as const])),
  ]);
}

/** Lean's rowValue. */
const rowValue = (fields: ReadonlyMap<string, string>, row: Fields): unknown =>
  Object.fromEntries(
    Object.entries(row).map(([k, x]) => {
      const entity = fields.get(k);
      return [k, entity !== undefined && typeof x === "string" ? new Ref(entity, x) : x];
    }),
  );

/** Lean's recordsValue. */
function recordsValue(st: Service, records: Records): unknown {
  return Object.fromEntries(
    st.entities.flatMap((e) => {
      const row = (r: Fields) => rowValue(keyFields(st, e), r);
      const single = records.singles.get(e);
      if (st.singles.includes(e)) return single === undefined ? [] : [[e, row(single.encoded)]];
      const rows = [...(records.keyed.get(e) ?? [])].toSorted(([a], [b]) => byCodePoint(a, b));
      return [[e, new Bag(rows.map(([, r]) => row(r.encoded)))]];
    }),
  );
}

/** Returns what the relation compares of a run: the violation that halted it, or its trace lines and records. */
export function outcomeOf(
  st: Service,
  halted: ViolationValue | null,
  lines: readonly TraceLine[],
  records: Records,
  created: ReadonlyMap<string, string>,
): Outcome {
  if (halted !== null) return { halted, lines: [], records: null, created: new Map() };
  return { halted: null, lines, records: recordsValue(st, records), created };
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

/** Lean's sameRecords. */
function sameRecords(set: readonly Binding[], original: Outcome, alternative: Outcome): Sameness {
  const values = renaming(
    original,
    alternative,
  )({ domain: () => "", fresh: new Set(original.created.keys()), image: () => true });
  return anySameness(set.map((b) => matchesSameness(matchValue(values, b, original.records, alternative.records))));
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
    return { aspect: "records", original: plain(original.records), alternative: plain(alternative.records) };
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
