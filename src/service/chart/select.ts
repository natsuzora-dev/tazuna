import type { Trigger } from "../../data/transitionRef.generated.ts";
import { canonicalJson, type Fields } from "../../data/values.ts";
import { transitionRef } from "../../spec/structure.ts";
import { isInside, leaves, pathOf } from "../../spec/tree.ts";
import { ref } from "../basic.ts";
import { Failed, firstFalse, issueViolation } from "../functions.ts";
import { copyId, type InstanceId, mapOf } from "../instance.ts";
import { valueName } from "../note.ts";
import { LazyRecordSource } from "../records.ts";
import {
  type Chosen,
  copyKeysOf,
  depth,
  documentOrder,
  halt,
  type Instance,
  machine,
  NoteAccess,
  type Run,
  type State,
  scopeOf,
} from "../state.ts";
import { type Chart, type Transition, transitionsAt } from "./basic.ts";
import { exitsOf } from "./config.ts";

interface Leaf {
  readonly holder: Instance;
  /** The leaf state, or undefined when only the chart's own transitions are searched. */
  readonly leaf: string | undefined;
}

export function choose(
  r: Run,
  instance: Instance,
  transitions: readonly Transition[],
  extra: Fields,
): Transition | undefined {
  return transitions.find((t) => passes(r, instance, t, extra));
}

/** Returns whether every guard condition of `t` holds, and reports the first false one as a coverage hit. */
function passes(r: Run, instance: Instance, t: Transition, extra: Fields): boolean {
  const scope = scopeOf(r.state, instance, t.source);
  const records = new LazyRecordSource(r.state.records, r.note);
  const transition = transitionRef(t);
  const definition = ref(r.st, instance.chart.name);
  const failing = firstFalse(
    (condition) => r.functions.guard(scope, records, transition, condition, extra, new NoteAccess(r, scope)),
    t.guards,
  );
  if (failing instanceof Failed) return halt(issueViolation(definition, failing));
  if (failing !== undefined)
    r.note.reached({ kind: "guardFalse", definition, data: { transition, condition: failing } });
  return failing === undefined;
}

export function reaches(r: Run, copy: Instance, payload: unknown): boolean {
  const map = mapOf(copy.id) as string;
  const key = r.functions.copyKey(copy.chart.name, map, payload);
  if (key instanceof Failed) return halt(issueViolation(ref(r.st, copy.chart.name), key));
  return key === undefined || (copy.id.kind === "copy" && key === canonicalJson(copy.id.key));
}

function exitKeys(s: State, c: Chosen): Set<string> {
  const keys = new Set<string>();
  for (const n of exitsOf(c.instance, c.t)) {
    keys.add(valueName({ kind: "state", id: c.instance.id, state: n }));
    for (const k of copyKeysOf(c.instance, n)) {
      const copy = copyId(c.instance.id, n, k);
      for (const m of machine(s, copy)?.entered.keys() ?? [])
        keys.add(valueName({ kind: "state", id: copy, state: m }));
    }
  }
  return keys;
}

/** SCXML removeConflictingTransitions. */
function removeConflicts(s: State, c: Chart, enabled: readonly Chosen[]): Chosen[] {
  const kept: Chosen[] = [];
  for (const t1 of enabled) {
    const exits1 = exitKeys(s, t1);
    const overlapping = kept.filter((t2) => [...exitKeys(s, t2)].some((k) => exits1.has(k)));
    if (overlapping.some((t2) => !isInside(c.tree, t1.t.source, t2.t.source))) continue;
    for (const t2 of overlapping) kept.splice(kept.indexOf(t2), 1);
    kept.push(t1);
  }
  return kept;
}

export function leavesOf(r: Run, instance: Instance, reached: (copy: Instance) => boolean, trigger?: Trigger): Leaf[] {
  const chart = instance.chart;
  const states = [...chart.states.values()];
  const reaching = new Map(
    [...instance.copyKeys].map(([map, keys]) => [
      map,
      keys.flatMap((k) => {
        const copy = machine(r.state, copyId(instance.id, map, k));
        return copy !== undefined && reached(copy) ? [copy] : [];
      }),
    ]),
  );
  if (trigger !== undefined) {
    const handling = states.filter((st) => transitionsAt(chart, st.name, trigger).length > 0).map((st) => st.name);
    r.note.readStates([
      ...[instance, ...[...reaching.values()].flat()].flatMap((holder) =>
        handling.map((n): [InstanceId, string] => [holder.id, n]),
      ),
      ...states
        .filter((state) => instance.entered.has(state.name) && state.kind === "map")
        .map((state): [InstanceId, string] => [instance.id, state.name]),
    ]);
  }
  const leavesOfHolder = new Map(
    [instance, ...[...reaching.values()].flat()].map((holder) => [holder, leaves(chart.tree, holder.entered)]),
  );
  const isLeaf = (holder: Instance, n: string) => leavesOfHolder.get(holder)?.includes(n) === true;
  const found = documentOrder(r.state, instance)
    .filter(({ holder, n }) =>
      holder === instance
        ? isLeaf(holder, n) && (reaching.get(n) ?? []).length === 0
        : (reaching.get(mapOf(holder.id) as string) ?? []).includes(holder) && isLeaf(holder, n),
    )
    .map(({ holder, n }) => ({ holder, leaf: n }));
  return found.length === 0 ? [{ holder: instance, leaf: undefined }] : found;
}

/** SCXML selectTransitions and selectEventlessTransitions. `trigger` is an `on` or `always` trigger. */
export function select(r: Run, instance: Instance, trigger: Trigger, extra: Fields, leaves: readonly Leaf[]): Chosen[] {
  const chart = instance.chart;
  const enabled: Chosen[] = [];
  for (const { holder, leaf } of leaves) {
    const path = leaf === undefined ? [] : pathOf(chart.tree, leaf);
    const holderDepth = depth(holder);
    const levels: { by: Instance; source: string | null; on: readonly Transition[] }[] = [];
    for (const [i, n] of [...path.entries()].reverse()) {
      const by = i < holderDepth ? instance : holder;
      levels.push({ by, source: n, on: transitionsAt(chart, n, trigger) });
    }
    levels.push({ by: instance, source: null, on: transitionsAt(chart, null, trigger) });
    for (const level of levels) {
      if (level.on.length === 0) continue;
      if (level.source !== null) r.note.readStates([[level.by.id, level.source]]);
      const found = choose(r, level.by, level.on, extra);
      if (found === undefined) continue;
      if (!enabled.some((c) => c.instance === level.by && c.t === found))
        enabled.push({ instance: level.by, t: found });
      break;
    }
  }
  return removeConflicts(r.state, chart, enabled);
}
