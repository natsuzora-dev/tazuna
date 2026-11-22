// This module follows computeExitSet and computeEntrySet of W3C SCXML Appendix D.
import { type ChartStructure, type StateStructure, stateNamed } from "./structure.ts";

function kindOf(chart: ChartStructure, name: string): StateStructure["kind"] | null {
  return stateNamed(chart, name)?.kind ?? null;
}

export function pathOf(chart: ChartStructure, name: string): readonly string[] {
  return stateNamed(chart, name)?.path ?? [];
}

/** Returns whether `name` is `ancestor` or a descendant of it. */
export function isDescendant(chart: ChartStructure, name: string, ancestor: string): boolean {
  return pathOf(chart, name).includes(ancestor);
}

function commonPrefix(a: readonly string[], b: readonly string[]): number {
  let common = 0;
  while (common < a.length && common < b.length && a[common] === b[common]) common += 1;
  return common;
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
