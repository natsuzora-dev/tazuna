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
import { byCodePoint, canonicalJson, type Fields, type Json, plain } from "../data/values.ts";
import type { ViolationValue } from "../data/violation.ts";
import type { Service } from "../service/basic.ts";
import { chartOf, type InstanceId, mapOf } from "../service/instance.ts";
import { stepNameDefinition } from "../service/note.ts";
import type { Records } from "../service/records.ts";
import type { Deadline, Instance, State } from "../service/state.ts";
import type { KeyPosition } from "../spec/structure.generated.ts";
import { chartStructure, stateNamed } from "../spec/structure.ts";

/** Lean's Settled: the outcome of a run that did not halt. */
export interface Settled {
  readonly lines: readonly TraceLine[];
  readonly records: unknown;
  readonly instances: Bag;
  readonly created: ReadonlyMap<string, string>;
}

/** Lean's Outcome: the violation that halted a run, or what it settled to. */
export type Outcome = { readonly halted: ViolationValue } | { readonly settled: Settled };

const haltedOf = (o: Outcome): ViolationValue | null => ("halted" in o ? o.halted : null);

/** Lean's refsAt: each key position that names a definition, its path as JSON text, with that definition's domain. */
const refsAt = (keys: readonly KeyPosition[] | undefined): ReadonlyMap<string, string> =>
  new Map(
    (keys ?? []).flatMap((k) =>
      k.entity === null ? [] : [[JSON.stringify(k.path), `${k.entity.service}/${k.entity.name}`] as const],
    ),
  );

/** Lean's keyPaths. */
function keyPaths(st: Service, e: string): ReadonlyMap<string, string> {
  const found = st.structure.definitions.find((d) => d.kind === "entity" && d.service === st.service && d.name === e);
  return refsAt(found?.kind === "entity" ? found.keys : undefined);
}

/** Lean's keyed. */
function keyed(keys: ReadonlyMap<string, string>, path: readonly string[], v: unknown): unknown {
  if (typeof v === "string") {
    const entity = keys.get(JSON.stringify(path));
    return entity === undefined ? v : new Ref(entity, v);
  }
  if (Array.isArray(v)) return v.map((x) => keyed(keys, path, x));
  if (v !== null && typeof v === "object")
    return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, keyed(keys, [...path, k], x)]));
  return v;
}

/** Lean's recordsValue. */
function recordsValue(st: Service, records: Records): unknown {
  return Object.fromEntries(
    st.entities.flatMap((e) => {
      const keys = keyPaths(st, e);
      const row = (r: Fields) => keyed(keys, [], r);
      const single = records.singles.get(e);
      if (st.singles.includes(e)) return single === undefined ? [] : [[e, row(single.encoded)]];
      const rows = [...(records.keyed.get(e) ?? [])].toSorted(([a], [b]) => byCodePoint(a, b));
      return [[e, new Bag(rows.map(([, r]) => row(r.encoded)))]];
    }),
  );
}

/** Lean's mapNamed. */
const mapNamed = (st: Service, chart: string, map: string) => {
  const c = chartStructure(st.structure, st.service, chart);
  return c === undefined ? undefined : stateNamed(c, map);
};

/** Lean's idValue. */
const idValue = (st: Service, id: InstanceId): unknown =>
  id.kind === "top"
    ? id
    : {
        kind: "copy",
        owner: idValue(st, id.owner),
        map: id.map,
        key: keyed(refsAt(mapNamed(st, chartOf(id.owner), id.map)?.itemKeys), [], id.key),
      };

const canonicalOrder = <T>(values: readonly T[]): T[] =>
  values.toSorted((a, b) => byCodePoint(canonicalJson(plain(a)), canonicalJson(plain(b))));

const names = (ns: Iterable<string>): string[] => [...ns].toSorted(byCodePoint);

/** Lean's instanceValue; `context` is the instance's context as JSON, as Lean holds it. */
function instanceValue(st: Service, deadlines: readonly Deadline[], i: Instance, context: Json): unknown {
  const map = mapOf(i.id);
  const contextKeys =
    map === undefined
      ? chartStructure(st.structure, st.service, chartOf(i.id))?.contextKeys
      : mapNamed(st, chartOf(i.id), map)?.contextKeys;
  return {
    id: idValue(st, i.id),
    states: names(i.entered.keys()),
    history: [...i.lastChildren].toSorted(([a], [b]) => byCodePoint(a, b)).map(([p, cs]) => [p, names(cs)]),
    context: keyed(refsAt(contextKeys), [], context),
    deadlines: canonicalOrder(
      deadlines
        .filter((d) => d.machine === i.id)
        .map((d) => ({ state: d.state, name: d.name, time: d.time.toString() })),
    ),
  };
}

/** Lean's instancesValue. */
const instancesValue = (st: Service, s: State, contextOf: (i: Instance) => Json): Bag =>
  new Bag(
    canonicalOrder(
      [...s.machines.values(), ...s.copies.values()]
        .filter((i) => !i.closed)
        .map((i) => instanceValue(st, s.deadlines, i, contextOf(i))),
    ),
  );

/** Lean's Outcome.of. `contextOf` encodes an instance's context, which Lean holds as JSON. */
export const outcomeOf = (
  st: Service,
  halted: ViolationValue | null,
  lines: readonly TraceLine[],
  s: State,
  created: ReadonlyMap<string, string>,
  contextOf: (i: Instance) => Json,
): Outcome =>
  halted !== null
    ? { halted }
    : {
        settled: { lines, records: recordsValue(st, s.records), instances: instancesValue(st, s, contextOf), created },
      };

/**
 * Lean's Compare: the first violation that verify finds in `actual`, with `expected` as the snapshot, or else the set of
 * bindings. `renamed` refines what verify knows of the values (renaming).
 */
export type Compare = (
  renamed: (v: Values) => Values,
  expected: readonly TraceLine[],
  actual: readonly TraceLine[],
) => { readonly mismatch: ViolationValue } | { readonly set: readonly Binding[] };

/** Lean's Settled.renaming. */
const renaming =
  (original: Settled, alternative: Settled) =>
  (v: Values): Values => ({
    ...v,
    domain: (s) => original.created.get(s) ?? v.domain(s),
    image: (s, t) => {
      const d = original.created.get(s);
      return d === undefined ? v.image(s, t) : alternative.created.get(t) === d;
    },
  });

/** Lean's Settled.state. */
const stateOf = (s: Settled): unknown => ({ records: s.records, instances: s.instances });

/** Lean's samePart. */
function samePart(
  part: (s: Settled) => unknown,
  set: readonly Binding[],
  original: Settled,
  alternative: Settled,
): Sameness {
  const values = renaming(
    original,
    alternative,
  )({ domain: () => "", fresh: new Set(original.created.keys()), image: () => true });
  return anySameness(set.map((b) => matchesSameness(matchValue(values, b, part(original), part(alternative)))));
}

type Of<K extends ChoiceDependent["kind"]> = Extract<ChoiceDependent, { readonly kind: K }>;

/** Returns the identity of a halting violation; two halting violations differ when their kinds or data differ. */
const haltIdentity = (v: ViolationValue | null): string | null => (v === null ? null : canonicalJson([v.kind, v.data]));

/** Lean's Comparison: no difference (`undefined`), a difference, or too many renamings to tell. */
type Comparison = Difference | "uncomparable" | undefined;

/** Lean's compareStates. */
function compareStates(set: readonly Binding[], original: Settled, alternative: Settled): Comparison {
  const same = samePart(stateOf, set, original, alternative);
  if (same === "same") return undefined;
  if (same === "uncomparable") return same;
  return samePart((s) => s.records, set, original, alternative) === "same"
    ? { aspect: "instances", original: plain(original.instances), alternative: plain(alternative.instances) }
    : { aspect: "records", original: plain(original.records), alternative: plain(alternative.records) };
}

/** Lean's difference. */
function difference(compare: Compare, original: Outcome, alternative: Outcome): Comparison {
  if (!("settled" in original) || !("settled" in alternative)) {
    const [o, a] = [haltedOf(original), haltedOf(alternative)];
    return haltIdentity(o) === haltIdentity(a) ? undefined : { aspect: "halt", original: o, alternative: a };
  }
  const [o, a] = [original.settled, alternative.settled];
  const compared = compare(renaming(o, a), o.lines, a.lines);
  if (!("mismatch" in compared)) return compareStates(compared.set, o, a);
  return "mismatch" in compare(renaming(o, o), o.lines, o.lines)
    ? compareStates([emptyBinding], o, a)
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
