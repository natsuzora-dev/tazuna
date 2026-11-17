import type { Fields } from "../../data/values.ts";
import { transitionRef } from "../../spec/structure.ts";
import { entryOrder, entrySet, historyTargets, parallelBetween } from "../../spec/tree.ts";
import { ref } from "../basic.ts";
import { mapOf } from "../instance.ts";
import { limits } from "../limits.ts";
import type { RegionPair } from "../note.ts";
import { type Chosen, depth, documentOrder, type Instance } from "../state.ts";
import { exitsOf } from "./config.ts";
import { addDeadlines } from "./deadline.ts";
import { closeFinal, enterFinal } from "./done.ts";
import { endWith, exitOne, recordHistory, runAssign } from "./exit.ts";
import { enter as enterQueue, type Processing } from "./queue.ts";

function sharedMap(a: Chosen, b: Chosen): string | null {
  const [ma, mb] = [mapOf(a.instance.id), mapOf(b.instance.id)];
  return ma !== undefined && a.instance !== b.instance && ma === mb ? ma : null;
}

function regionPairOf(instance: Instance, a: Chosen, b: Chosen, j: number, k: number): RegionPair | null {
  const pair = (state: string): RegionPair => ({
    first: j,
    second: k,
    firstRef: transitionRef(a.t),
    secondRef: transitionRef(b.t),
    state,
  });
  const map = sharedMap(a, b);
  if (map !== null) return pair(map);
  if (a.t.source === null || b.t.source === null) return null;
  const parallel = parallelBetween(instance.chart.tree, a.t.source, b.t.source);
  return parallel === null ? null : pair(parallel);
}

/**
 * Returns the pairs of transitions in different regions or copies within one microstep, which are checked for
 * conflicts. SCXML lets the later write win, but regions act simultaneously and copies have no order, so write order
 * has no meaning. Such pairs are conflicts instead, as in Statemate (two writes, or a write and a read, of one value in
 * a step conflict) and Esterel (a single-valued signal emitted twice in a reaction is rejected).
 */
function regionPairs(instance: Instance, chosen: readonly Chosen[]): RegionPair[] {
  return chosen.flatMap((b, k) =>
    chosen.slice(0, k).flatMap((a, j) => {
      const pair = regionPairOf(instance, a, b, j, k);
      return pair === null ? [] : [pair];
    }),
  );
}

function enterOne(r: Processing, instance: Instance, name: string, step: number): void {
  const state = instance.chart.states.get(name);
  if (state === undefined) return;
  r.note.wroteState(instance.id, name);
  instance.entered.set(name, r.state.now);
  r.note.reached({ kind: "state", definition: ref(r.st, instance.chart.name), data: { state: name } });
  runAssign(r, instance, { kind: "entry", state: name }, {}, name);
  if (state.kind === "final") {
    if (state.parent !== null) enterFinal(r, instance, state.parent, step);
    else if (instance.chart.screen) closeFinal(r, instance, step);
    else endWith(r, instance.id, limits.exitDepth);
    return;
  }
  addDeadlines(r.state, instance.id, name, r.functions.deadlines(instance.chart.name, name));
  if (state.activities.length > 0) enterQueue(r.queue, instance.id, name, step);
}

/** SCXML enterStates. */
export function enter(r: Processing, instance: Instance, targets: readonly string[], step: number): void {
  for (const name of entryOrder(instance.chart.tree, entering(instance, targets))) enterOne(r, instance, name, step);
}

function entering(instance: Instance, targets: readonly string[]): Set<string> {
  return new Set(targets.flatMap((target) => entrySet(instance.chart.tree, instance.entered, depth(instance), target)));
}

export function microstep(
  r: Processing,
  instance: Instance,
  chosen: readonly Chosen[],
  extra: Fields,
  step: number,
): void {
  if (instance.closed) return;
  for (const c of chosen)
    r.note.reached({
      kind: "transition",
      definition: ref(r.st, instance.chart.name),
      data: { transition: transitionRef(c.t) },
    });
  const order = documentOrder(r.state, instance);
  const inOrder = (sets: readonly ReadonlySet<string>[]) =>
    order.flatMap(({ holder, n }) => {
      const k = chosen.findIndex((c, j) => c.instance === holder && sets[j]?.has(n));
      return k < 0 ? [] : [{ holder, n, k }];
    });
  const pairs = regionPairs(instance, chosen);
  const exiting = inOrder(chosen.map((c) => new Set(exitsOf(c.instance, c.t)))).toReversed();
  for (const e of exiting) recordHistory(e.holder, e.n);
  for (const e of exiting) {
    r.note.transitionPart(e.k);
    exitOne(r, limits.exitDepth, e.holder, e.n);
  }
  for (const [k, c] of chosen.entries()) {
    r.note.transitionPart(k);
    runAssign(r, c.instance, { kind: "transition", transition: transitionRef(c.t) }, extra, c.t.source);
  }
  const entries = chosen.map((c) =>
    c.t.target === null
      ? new Set<string>()
      : entering(
          c.instance,
          historyTargets(c.instance.chart.tree, c.instance.chart.initial, c.instance.lastChildren, c.t.target),
        ),
  );
  for (const e of inOrder(entries)) {
    r.note.transitionPart(e.k);
    enterOne(r, e.holder, e.n, step);
  }
  r.note.microstepEnds({ chart: ref(r.st, instance.chart.name), pairs });
}
