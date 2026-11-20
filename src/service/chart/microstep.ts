import type { Fields } from "../../data/values.ts";
import { hasParameters, transitionRef } from "../../spec/structure.ts";
import { entryOrder, entrySet, historyTargets, parallelBetween } from "../../spec/tree.ts";
import { ref } from "../basic.ts";
import { type Edge, Failed, issueViolation } from "../functions.ts";
import { mapOf } from "../instance.ts";
import type { RegionPair } from "../note.ts";
import { LazyRecordSource } from "../records.ts";
import {
  type Chosen,
  depth,
  documentOrder,
  halt,
  heldAt,
  type Instance,
  machine,
  NoteAccess,
  scopeOf,
} from "../state.ts";
import { exitsOf } from "./config.ts";
import { addDeadlines } from "./deadline.ts";
import { closeFinal, enterFinal } from "./done.ts";
import { endWith, exitFuel, exitOne, recordHistory, runAssign } from "./exit.ts";
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

/** Lean's fillHeld: the edge `edge` fills the parameters of state `n`, which it enters, with its `with`. */
function fillHeld(
  r: Processing,
  instance: Instance,
  n: string,
  edge: Edge,
  state: string | null,
  held: Fields | undefined,
  extra: Fields,
): void {
  const scope = scopeOf(r.state, instance, state, held);
  const records = new LazyRecordSource(r.state.records, r.note);
  const filled = r.functions.held(scope, records, n, edge, extra, new NoteAccess(r, scope));
  const chart = ref(r.st, instance.chart.name);
  if (filled instanceof Failed) halt(issueViolation(chart, filled));
  instance.held.set(n, r.functions.decode({ kind: "held", chart, state: n }, filled));
}

/**
 * Lean's fillByTransition: transition `c` fills the parameters of its target with its `with`, when `entered`, the states
 * that `c` enters, holds a target that has parameters.
 */
function fillByTransition(r: Processing, c: Chosen, entered: ReadonlySet<string>, held: Fields, extra: Fields): void {
  const target = c.t.target;
  if (target === null || machine(r.state, c.instance.id) === undefined) return;
  const state = c.instance.chart.states.get(target);
  if (state === undefined || !hasParameters(state.spec) || !entered.has(target)) return;
  fillHeld(r, c.instance, target, { kind: "transition", transition: transitionRef(c.t) }, c.t.source, held, extra);
}

/** Lean's fillByInitial: the parent's initial edge fills the parameters of `n`, unless a transition `filled` them. */
function fillByInitial(r: Processing, instance: Instance, n: string, filled: boolean): void {
  const state = instance.chart.states.get(n);
  if (state === undefined || state.spec.parent === null || !hasParameters(state.spec) || filled) return;
  fillHeld(r, instance, n, { kind: "initial", parent: state.spec.parent }, state.spec.parent, undefined, {});
}

/** Lean's enterOne; `filled` is as in fillByInitial. */
function enterOne(r: Processing, instance: Instance, name: string, step: number, filled: boolean): void {
  const state = instance.chart.states.get(name);
  if (state === undefined) return;
  r.note.wroteState(instance.id, name);
  instance.entered.set(name, r.state.now);
  r.note.reached({ kind: "state", definition: ref(r.st, instance.chart.name), data: { state: name } });
  fillByInitial(r, instance, name, filled);
  runAssign(r, instance, { kind: "entry", state: name }, {}, name);
  if (state.spec.kind === "final") {
    if (state.spec.parent !== null) enterFinal(r, instance, state.spec.parent, step);
    else if (instance.chart.screen) closeFinal(r, instance, step);
    else endWith(r, instance.id, exitFuel(r.st));
    return;
  }
  addDeadlines(r, instance, name, state.spec.deadlines, step);
  if (state.activities.length > 0) enterQueue(r.queue, instance.id, name, step);
}

/** SCXML enterStates. */
export function enter(r: Processing, instance: Instance, targets: readonly string[], step: number): void {
  for (const name of entryOrder(instance.chart.tree, entering(instance, targets)))
    enterOne(r, instance, name, step, false);
}

function entering(instance: Instance, targets: readonly string[]): Set<string> {
  return new Set(targets.flatMap((target) => entrySet(instance.chart.tree, instance.entered, depth(instance), target)));
}

/** Lean's State.entryPairsOf: the states that transition `c` enters, from the instance's current states. */
function entriesOf(c: Chosen): Set<string> {
  return c.t.target === null
    ? new Set<string>()
    : entering(
        c.instance,
        historyTargets(c.instance.chart.tree, c.instance.chart.initial, c.instance.lastChildren, c.t.target),
      );
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
  const sourceHeld = chosen.map((c) => heldAt(c.instance, c.t.source));
  const exiting = inOrder(chosen.map((c) => new Set(exitsOf(c.instance, c.t)))).toReversed();
  for (const e of exiting) recordHistory(e.holder, e.n);
  for (const e of exiting) {
    r.note.transitionPart(e.k);
    exitOne(r, exitFuel(r.st), e.holder, e.n);
  }
  const entries = chosen.map(entriesOf);
  for (const [k, c] of chosen.entries()) {
    r.note.transitionPart(k);
    const held = sourceHeld[k] ?? {};
    fillByTransition(r, c, entries[k] ?? new Set(), held, extra);
    runAssign(r, c.instance, { kind: "transition", transition: transitionRef(c.t) }, extra, c.t.source, held);
  }
  for (const e of inOrder(entries)) {
    r.note.transitionPart(e.k);
    const c = chosen[e.k];
    enterOne(r, e.holder, e.n, step, c?.instance === e.holder && c.t.target === e.n);
  }
  r.note.microstepEnds({ chart: ref(r.st, instance.chart.name), pairs });
}
