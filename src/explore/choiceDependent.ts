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
import type { Undecided } from "../data/undecided.generated.ts";
import { byCodePoint, canonicalJson, type Fields, type Json, plain } from "../data/values.ts";
import type { ViolationValue } from "../data/violation.ts";
import type { Schema, Service } from "../service/basic.ts";
import { chartOf, type InstanceId, mapOf } from "../service/instance.ts";
import { stepNameDefinition } from "../service/note.ts";
import type { Records } from "../service/records.ts";
import type { Deadline, Instance, State } from "../service/state.ts";
import type { KeyPosition } from "../spec/structure.generated.ts";
import { chartStructure, mapStateOf, stateNamed } from "../spec/structure.ts";

/** Lean's Finished: the outcome of a run that did not halt. */
export interface Finished {
  readonly lines: readonly TraceLine[];
  readonly state: unknown;
  readonly created: ReadonlyMap<string, string>;
}

/** Lean's Outcome: the violation that halted a run, or how it finished. */
export type Outcome = { readonly halted: ViolationValue } | { readonly finished: Finished };

/**
 * Encodes a value of `schema` as JSON, as Lean holds it. TS holds an instance's context decoded, so the view encodes it
 * where Lean reads it as it is.
 */
export type Encode = (schema: Schema, value: unknown) => Json;

/** Lean's Outcome.halted?. */
const haltedOf = (o: Outcome): ViolationValue | null => ("halted" in o ? o.halted : null);

/** Lean's refsAt, with each path as JSON text. */
const refsAt = (keys: readonly KeyPosition[] | undefined): ReadonlyMap<string, string> =>
  new Map((keys ?? []).map((k) => [JSON.stringify(k.path), `${k.entity.service}/${k.entity.name}`] as const));

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
    st.recordKeys.flatMap(([e, positions]) => {
      const keys = refsAt(positions);
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
const idValue = (st: Service, id: InstanceId): unknown => {
  switch (id.kind) {
    case "top":
      return id;
    case "opened":
      return { ...id, opener: idValue(st, id.opener) };
    case "copy":
      return {
        kind: "copy",
        owner: idValue(st, id.owner),
        map: id.map,
        key: keyed(refsAt(mapStateOf(mapNamed(st, chartOf(id.owner), id.map))?.itemKeys), [], id.key),
      };
  }
};

const canonicalOrder = <T>(values: readonly T[]): T[] =>
  values.toSorted((a, b) => byCodePoint(canonicalJson(plain(a)), canonicalJson(plain(b))));

const names = (ns: Iterable<string>): string[] => [...ns].toSorted(byCodePoint);

/** Lean's instanceValue. */
function instanceValue(st: Service, deadlines: readonly Deadline[], i: Instance, encode: Encode): unknown {
  const map = mapOf(i.id);
  const chart = { service: st.service, name: chartOf(i.id) };
  const contextKeys =
    map === undefined
      ? chartStructure(st.structure, st.service, chart.name)?.contextKeys
      : mapStateOf(mapNamed(st, chart.name, map))?.contextKeys;
  const context = encode(
    map === undefined ? { kind: "context", chart } : { kind: "mapContext", chart, map },
    i.context,
  );
  return {
    id: idValue(st, i.id),
    states: names(i.entered.keys()),
    history: [...i.lastChildren].toSorted(([a], [b]) => byCodePoint(a, b)).map(([p, cs]) => [p, names(cs)]),
    context: keyed(refsAt(contextKeys), [], context),
    held: Object.fromEntries(
      [...i.held]
        .toSorted(([a], [b]) => byCodePoint(a, b))
        .map(([state, fields]) => {
          const encoded = encode({ kind: "held", chart, state }, fields) as Fields;
          const c = chartStructure(st.structure, st.service, chart.name);
          return [state, keyed(refsAt(c === undefined ? undefined : stateNamed(c, state)?.held?.keys), [], encoded)];
        }),
    ),
    deadlines: canonicalOrder(
      deadlines.filter((d) => d.machine === i.id).map((d) => ({ state: d.state, name: d.name, time: d.time })),
    ),
  };
}

/** Lean's instancesValue. */
const instancesValue = (st: Service, s: State, encode: Encode): Bag =>
  new Bag(
    canonicalOrder(
      [...s.machines.values(), ...s.copies.values()]
        .filter((i) => !i.closed)
        .map((i) => instanceValue(st, s.deadlines, i, encode)),
    ),
  );

/** Lean's stateValue. */
export const stateValue = (st: Service, s: State, encode: Encode): unknown => ({
  records: recordsValue(st, s.records),
  instances: instancesValue(st, s, encode),
});

/** Lean's Outcome.of. */
export const outcomeOf = (
  st: Service,
  halted: ViolationValue | null,
  lines: readonly TraceLine[],
  s: State,
  created: ReadonlyMap<string, string>,
  encode: Encode,
): Outcome => (halted !== null ? { halted } : { finished: { lines, state: stateValue(st, s, encode), created } });

/**
 * Lean's Compare: the difference in outputs that verify finds first in `actual`, with `expected` as the snapshot, a
 * violation or an `after` that differs, or else the set of bindings. `renamed` refines what verify knows of the values
 * (renaming).
 */
export type Compare = (
  renamed: (v: Values) => Values,
  expected: readonly TraceLine[],
  actual: readonly TraceLine[],
) => { readonly difference: Difference } | { readonly set: readonly Binding[] };

/** Lean's Finished.renaming. */
const renaming =
  (original: Finished, alternative: Finished) =>
  (v: Values): Values => ({
    ...v,
    domain: (s) => original.created.get(s) ?? v.domain(s),
    image: (s, t) => {
      const d = original.created.get(s);
      return d === undefined ? v.image(s, t) : alternative.created.get(t) === d;
    },
  });

/** Lean's sameState. */
function sameState(set: readonly Binding[], original: Finished, alternative: Finished): Sameness {
  const values = renaming(
    original,
    alternative,
  )({ domain: () => "", fresh: new Set(original.created.keys()), image: () => true });
  return anySameness(set.map((b) => matchesSameness(matchValue(values, b, original.state, alternative.state))));
}

/** Returns the identity of a halting violation; two halting violations differ when their kinds or data differ. */
const haltIdentity = (v: ViolationValue | null): string | null => (v === null ? null : canonicalJson([v.kind, v.data]));

/** Lean's Comparison: no difference (`undefined`), a difference, or too many renamings to tell. */
type Comparison = Difference | "uncomparable" | undefined;

/** Lean's compareStates. */
function compareStates(set: readonly Binding[], original: Finished, alternative: Finished): Comparison {
  const same = sameState(set, original, alternative);
  if (same === "same") return undefined;
  if (same === "uncomparable") return same;
  return { aspect: "state", original: plain(original.state), alternative: plain(alternative.state) };
}

/** Lean's difference. */
function difference(compare: Compare, original: Outcome, alternative: Outcome): Comparison {
  if (!("finished" in original) || !("finished" in alternative)) {
    const [o, a] = [haltedOf(original), haltedOf(alternative)];
    return haltIdentity(o) === haltIdentity(a) ? undefined : { aspect: "halt", original: o, alternative: a };
  }
  const [o, a] = [original.finished, alternative.finished];
  const compared = compare(renaming(o, a), o.lines, a.lines);
  if (!("difference" in compared)) return compareStates(compared.set, o, a);
  return "difference" in compare(renaming(o, o), o.lines, o.lines)
    ? compareStates([emptyBinding], o, a)
    : compared.difference;
}

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
): ChoiceDependent | Undecided | undefined {
  const [first, second, originalOrder, alternativeOrder, original, alternative] =
    byCodePoint(canonicalJson(a), canonicalJson(b)) <= 0
      ? [a, b, aOrder, bOrder, aFirst, bFirst]
      : [b, a, bOrder, aOrder, bFirst, aFirst];
  const found = difference(compare, original, alternative);
  if (found === "uncomparable")
    return {
      kind: "Undecided.stepOrderBindings",
      definition: stepNameDefinition(service, first),
      data: { limit: bindingLimit },
    };
  return found === undefined
    ? undefined
    : {
        kind: "ChoiceDependent.stepOrder",
        definition: stepNameDefinition(service, first),
        data: { firstStep: first, secondStep: second, originalOrder, alternativeOrder, difference: found },
      };
}
