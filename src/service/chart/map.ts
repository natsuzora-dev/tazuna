import { limits } from "../../data/limits.generated.ts";
import { byCodePoint, plain } from "../../data/values.ts";
import { ref } from "../basic.ts";
import { Failed, type Functions, issueViolation } from "../functions.ts";
import { copyId } from "../instance.ts";
import { LazyRecordSource } from "../records.ts";
import { copyKeysOf, halt, type Instance, inStep, NoteAccess, newStep, report, scopeOf } from "../state.ts";
import { endWith } from "./exit.ts";
import { enter } from "./microstep.ts";
import type { Processing } from "./queue.ts";

/**
 * Starts a copy. The new copy replaces a closed copy with the same id and, as in Lean's list, comes last in
 * `copies`.
 */
function startCopy(r: Processing, owner: Instance, map: string, key: unknown, encodedKey: string, step: number): void {
  const id = copyId(owner.id, map, encodedKey);
  const copy: Instance = {
    chart: owner.chart,
    id,
    context: r.functions.copyContext(owner.chart.name, map),
    input: owner.input,
    entered: new Map(),
    lastChildren: new Map(),
    closed: false,
    awaitingOnDone: undefined,
    shown: new Map(),
    itemKey: key,
    copyKeys: new Map(),
  };
  r.state.copies.delete(id);
  r.state.copies.set(id, copy);
  const copyStep = newStep(r.state, { kind: "caused", cause: step });
  const initial = owner.chart.states.get(map)?.initial;
  inStep(r, copyStep, { kind: "start", id }, id, () => {
    if (initial !== null && initial !== undefined) enter(r, copy, [initial], copyStep);
  });
}

/** Returns whether the copy set of any map state changed. */
export function syncCopies(r: Processing, owner: Instance, step: number): boolean {
  const { evaluations } = r;
  let changed = false;
  for (const map of [...owner.entered.keys()]) {
    const part = `items of ${map}`;
    if (owner.chart.states.get(map)?.kind !== "map" || evaluations.replayIfFresh(owner.id, part)) continue;
    const definition = ref(r.st, owner.chart.name);
    let checked: ReturnType<Functions["items"]> = [];
    const reads = evaluations.track(() => {
      r.note.readStates([[owner.id, map]]);
      const scope = scopeOf(r.state, owner, map);
      checked = r.functions.items(scope, new LazyRecordSource(r.state.records, r.note), new NoteAccess(r, scope));
    });
    if (checked instanceof Failed)
      return halt(
        issueViolation(definition, checked, () => ({ kind: "Fault.itemsSchema", definition, data: { map } })),
      );
    const keys = checked.toSorted((a, b) => byCodePoint(a.encodedKey, b.encodedKey));
    const duplicate = keys.find((k, i) => keys.findIndex((other) => other.encodedKey === k.encodedKey) < i);
    if (duplicate !== undefined)
      report(r.state, { kind: "Fault.duplicateItemKey", definition, data: { map, itemKey: plain(duplicate.encoded) } });
    const current = copyKeysOf(owner, map);
    const itemKeys = keys.map((k) => k.encodedKey);
    const same = current.length === itemKeys.length && itemKeys.every((k, i) => current[i] === k);
    // The copy set is part of being in the map state; this write does not make the items evaluation stale.
    if (!same) r.note.wroteCopies(owner.id, map);
    evaluations.remember(owner.id, part, reads, reads);
    if (same) continue;
    changed = true;
    for (const k of current.toReversed())
      if (!itemKeys.includes(k)) endWith(r, copyId(owner.id, map, k), limits.exitDepth);
    for (const { key, encodedKey } of keys)
      if (!current.includes(encodedKey)) startCopy(r, owner, map, key, encodedKey, step);
    owner.copyKeys.set(map, itemKeys);
  }
  return changed;
}
