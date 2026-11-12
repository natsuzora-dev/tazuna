import type { TransitionRef } from "../data/transitionRef.ts";
import type { ChartStructure } from "../syntax/structure.ts";
import { pathOf } from "../syntax/tree.ts";
import type { ChartSpec, Definition, StateSpec, TransitionSpec } from "./definition.ts";

export function chartOf(d: Definition): ChartSpec | undefined {
  return d.kind === "machine" || d.kind === "screen" ? (d as unknown as ChartSpec) : undefined;
}

export interface TransitionArray {
  readonly keys: readonly string[];
  readonly transitions: readonly TransitionSpec[];
}

function completionTransitions(node: StateSpec): TransitionArray[] {
  const of = (keys: readonly string[], transitions: readonly TransitionSpec[] | undefined) =>
    transitions === undefined ? [] : [{ keys, transitions }];
  return [
    ...Object.entries(node.calls ?? {}).flatMap(([name, c]) => [
      ...of(["calls", name, "onFulfilled"], c.onFulfilled),
      ...of(["calls", name, "onRejected"], c.onRejected),
    ]),
    ...Object.entries(node.sends ?? {}).flatMap(([name, c]) => [
      ...of(["sends", name, "onAccepted"], c.onAccepted),
      ...of(["sends", name, "onRejected"], c.onRejected),
    ]),
    ...Object.entries(node.opens ?? {}).flatMap(([name, o]) => of(["opens", name, "onDone"], o.onDone)),
    ...of(["onDone"], node.onDone),
  ];
}

export function transitionArrays(node: StateSpec): TransitionArray[] {
  return [
    ...Object.entries(node.on ?? {}).map(([key, transitions]) => ({ keys: ["on", key], transitions })),
    ...Object.entries(node.after ?? {}).map(([name, d]) => ({
      keys: ["after", name, "onFired"],
      transitions: d.onFired,
    })),
    ...(node.always === undefined ? [] : [{ keys: ["always"], transitions: node.always }]),
    ...completionTransitions(node),
  ];
}

export function stateAt(chart: ChartSpec, path: readonly string[]): StateSpec {
  return path.reduce<StateSpec>((node, name) => node.states?.[name] as StateSpec, { states: chart.states });
}

export function transitionAt(chart: ChartSpec, structure: ChartStructure, t: TransitionRef): TransitionSpec {
  const node = t.state === null ? { on: chart.on } : stateAt(chart, pathOf(structure, t.state));
  const transitions = t.keys.reduce<unknown>((value, key) => (value as Record<string, unknown>)[key], node);
  return (transitions as readonly TransitionSpec[])[t.index] as TransitionSpec;
}
