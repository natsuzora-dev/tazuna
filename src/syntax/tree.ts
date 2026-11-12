// This module follows computeExitSet and computeEntrySet of W3C SCXML Appendix D.
import { type ChartStructure, type StateStructure, stateNamed } from "./structure.ts";

type Names = Pick<ReadonlySet<string>, "has">;

export function kindOf(chart: ChartStructure, name: string): StateStructure["kind"] | null {
  return stateNamed(chart, name)?.kind ?? null;
}

export function pathOf(chart: ChartStructure, name: string): readonly string[] {
  return stateNamed(chart, name)?.path ?? [];
}

function parentOf(chart: ChartStructure, name: string): string | null {
  return stateNamed(chart, name)?.parent ?? null;
}

/** Returns whether `name` is `ancestor` or a descendant of it. */
export function isDescendant(chart: ChartStructure, name: string, ancestor: string): boolean {
  return pathOf(chart, name).includes(ancestor);
}

export function descendants(chart: ChartStructure, name: string): string[] {
  return chart.states.filter((d) => d.name !== name && isDescendant(chart, d.name, name)).map((d) => d.name);
}

export function enterable(chart: ChartStructure, name: string): string[] {
  return (stateNamed(chart, name)?.children ?? []).filter((child) => kindOf(chart, child) !== "history");
}

function commonPrefix(a: readonly string[], b: readonly string[]): number {
  let common = 0;
  while (common < a.length && common < b.length && a[common] === b[common]) common += 1;
  return common;
}

/** Returns the count of the first `k` names of `path` without its trailing parallel states. */
function withoutParallel(chart: ChartStructure, path: readonly string[], k: number): number {
  return k > 0 && kindOf(chart, path[k - 1] as string) === "parallel" ? withoutParallel(chart, path, k - 1) : k;
}

/**
 * Returns the depth of the transition domain (SCXML) from the root; 0 is the whole chart. For a target that is the
 * source or its descendant, the domain is the source with `reenter: false` and the source's parent with `reenter: true`
 * (XState v5 reenter). Otherwise it is the nearest ancestor of both, or the target's parent when the target is a proper
 * ancestor of the source (SCXML findLCCA; even SCXML `type="internal"` exits and re-enters the source for a transition
 * to the source or an ancestor). A parallel state exits and enters all its regions together, so the domain widens to
 * its parent, except when `reenter: false` makes the source the domain.
 */
export function domainDepth(chart: ChartStructure, source: string | null, target: string, reenter: boolean): number {
  const targetPath = pathOf(chart, target);
  const sourcePath = source === null ? [] : pathOf(chart, source);
  const common = commonPrefix(targetPath, sourcePath);
  if (common === sourcePath.length)
    return reenter ? withoutParallel(chart, targetPath, Math.max(common - 1, 0)) : common;
  return withoutParallel(chart, targetPath, common === targetPath.length ? Math.max(common - 1, 0) : common);
}

/** Returns `names` in SCXML exitOrder: reverse document order. */
export function exitOrder(chart: ChartStructure, names: Names): string[] {
  return chart.states
    .map((s) => s.name)
    .toReversed()
    .filter((n) => names.has(n));
}

export function exitSet(
  chart: ChartStructure,
  entered: Names,
  source: string | null,
  target: string,
  reenter: boolean,
): string[] {
  const common = domainDepth(chart, source, target, reenter);
  const domain = common === 0 ? undefined : pathOf(chart, target)[common - 1];
  return exitOrder(chart, entered).filter(
    (n) => n !== domain && (domain === undefined || isDescendant(chart, n, domain)),
  );
}

function defaultChildren(chart: ChartStructure, name: string, state: StateStructure): string[] {
  if (state.kind === "parallel") return enterable(chart, name);
  return state.initial === null ? [] : [state.initial];
}

/**
 * Adds the default descendants of `name` to `acc`. Copies enter a map state's children, so a map state has no default
 * descendants.
 */
function addDefaults(chart: ChartStructure, name: string, acc: Set<string>): void {
  const state = stateNamed(chart, name);
  if (state === undefined || state.kind === "map") return;
  for (const child of defaultChildren(chart, name, state)) {
    acc.add(child);
    addDefaults(chart, child, acc);
  }
}

/**
 * Adds to `acc` `name` and its ancestors not yet entered, the other regions of ancestor parallel states with their
 * defaults, and the defaults of `name`. A copy does not enter its first `depth` ancestors from the root (the map state
 * and above).
 */
export function addEntrySet(
  chart: ChartStructure,
  entered: Names,
  depth: number,
  name: string,
  acc: Set<string>,
): void {
  const found = stateNamed(chart, name);
  if (found === undefined) return;
  for (const n of found.path.slice(depth)) if (!entered.has(n)) acc.add(n);
  for (const [i, n] of found.path.entries())
    if (depth <= i && kindOf(chart, n) === "parallel")
      for (const region of enterable(chart, n))
        if (region !== found.path[i + 1] && !entered.has(region) && !acc.has(region)) {
          acc.add(region);
          addDefaults(chart, region, acc);
        }
  addDefaults(chart, name, acc);
}

/** Returns `names` in SCXML entryOrder: document order. */
export function entryOrder(chart: ChartStructure, names: Names): string[] {
  return chart.states.map((s) => s.name).filter((n) => names.has(n));
}

export function entrySet(chart: ChartStructure, entered: Names, depth: number, name: string): string[] {
  const acc = new Set<string>();
  addEntrySet(chart, entered, depth, name, acc);
  return entryOrder(chart, acc);
}

/**
 * Returns the states that a transition to `target` enters. For an SCXML history state, they are the children active
 * when the parent was last exited, or the parent and its defaults if it never was. Copies never exit or enter their map
 * state, so a history state under a map state enters the map state's initial.
 */
export function historyTargets(
  chart: ChartStructure,
  initial: string,
  lastChildren: ReadonlyMap<string, readonly string[]>,
  target: string,
): readonly string[] {
  const state = stateNamed(chart, target);
  if (state?.kind !== "history") return [target];
  if (state.parent === null) return [initial];
  const recorded = lastChildren.get(state.parent) ?? [];
  if (recorded.length > 0) return recorded;
  const parent = stateNamed(chart, state.parent);
  if (parent?.kind !== "map") return [state.parent];
  return parent.initial === null ? [] : [parent.initial];
}

export function recordedChildren(chart: ChartStructure, entered: Names, name: string): string[] | null {
  const state = stateNamed(chart, name);
  if (state === undefined || state.children.length === 0) return null;
  return enterable(chart, name).filter((n) => entered.has(n));
}

function isDone(chart: ChartStructure, entered: Names, name: string): boolean {
  const state = stateNamed(chart, name);
  if (state === undefined) return false;
  if (state.kind === "parallel") return enterable(chart, name).every((r) => isDone(chart, entered, r));
  return state.children.some((n) => kindOf(chart, n) === "final" && entered.has(n));
}

function doneAncestors(chart: ChartStructure, entered: Names, up: string | null): string[] {
  if (up === null) return [];
  const state = stateNamed(chart, up);
  if (state === undefined || state.kind !== "parallel" || !isDone(chart, entered, up)) return [];
  return state.parent === null ? [up] : [up, ...doneAncestors(chart, entered, state.parent)];
}

/** Returns `parent` and its finished parallel ancestors, in finishing order, like SCXML done.state events. */
export function finished(chart: ChartStructure, entered: Names, parent: string): string[] {
  return [parent, ...doneAncestors(chart, entered, parentOf(chart, parent))];
}

export function leaves(chart: ChartStructure, entered: Names): string[] {
  return chart.states
    .filter((s) => entered.has(s.name) && !enterable(chart, s.name).some((c) => entered.has(c)))
    .map((s) => s.name);
}

export function isInside(chart: ChartStructure, inner: string | null, outer: string | null): boolean {
  if (inner === null) return false;
  if (outer === null) return true;
  return inner !== outer && isDescendant(chart, inner, outer);
}

/** Returns the parallel state whose different regions hold `a` and `b`. */
export function parallelBetween(chart: ChartStructure, a: string, b: string): string | null {
  const pa = pathOf(chart, a);
  const pb = pathOf(chart, b);
  const common = commonPrefix(pa, pb);
  if (common === 0 || common === pa.length || common === pb.length) return null;
  const parallel = pa[common - 1] as string;
  return kindOf(chart, parallel) === "parallel" ? parallel : null;
}
