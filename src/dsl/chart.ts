import type { TransitionRef, Trigger } from "../data/transitionRef.generated.ts";
import type { ChartStructure } from "../spec/structure.ts";
import { pathOf } from "../spec/tree.ts";
import type { ChartSpec, Definition, StateSpec, TransitionSpec } from "./definition.ts";

export function chartOf(d: Definition): ChartSpec | undefined {
  return d.kind === "machine" || d.kind === "screen" ? d : undefined;
}

export interface TransitionArray {
  readonly trigger: Trigger;
  readonly transitions: readonly TransitionSpec[];
}

/** The keys under which a state writes the transition array on `trigger`. */
export function pathOfTrigger(trigger: Trigger): readonly string[] {
  switch (trigger.type) {
    case "on":
      return ["on", trigger.key];
    case "after":
      return ["after", trigger.deadline, "onFired"];
    case "always":
    case "onDone":
      return [trigger.type];
    case "calls":
    case "sends":
      return [trigger.type, trigger.key, trigger.outcome];
    case "opens":
      return ["opens", trigger.key, "onDone"];
  }
}

function completionTransitions(node: StateSpec): TransitionArray[] {
  const of = (trigger: Trigger, transitions: readonly TransitionSpec[] | undefined) =>
    transitions === undefined ? [] : [{ trigger, transitions }];
  return [
    ...Object.entries(node.calls ?? {}).flatMap(([key, c]) => [
      ...of({ type: "calls", key, outcome: "onFulfilled" }, c.onFulfilled),
      ...of({ type: "calls", key, outcome: "onRejected" }, c.onRejected),
    ]),
    ...Object.entries(node.sends ?? {}).flatMap(([key, c]) => [
      ...of({ type: "sends", key, outcome: "onAccepted" }, c.onAccepted),
      ...of({ type: "sends", key, outcome: "onRejected" }, c.onRejected),
    ]),
    ...Object.entries(node.opens ?? {}).flatMap(([key, o]) => of({ type: "opens", key }, o.onDone)),
    ...of({ type: "onDone" }, node.onDone),
  ];
}

export function transitionArrays(node: StateSpec): TransitionArray[] {
  return [
    ...Object.entries(node.on ?? {}).map(([key, transitions]) => ({
      trigger: { type: "on", key } as const,
      transitions,
    })),
    ...Object.entries(node.after ?? {}).map(([deadline, d]) => ({
      trigger: { type: "after", deadline } as const,
      transitions: d.onFired,
    })),
    ...(node.always === undefined ? [] : [{ trigger: { type: "always" } as const, transitions: node.always }]),
    ...completionTransitions(node),
  ];
}

export function stateAt(chart: ChartSpec, path: readonly string[]): StateSpec {
  return path.reduce<StateSpec>((node, name) => node.states?.[name] as StateSpec, { states: chart.states });
}

export function transitionAt(chart: ChartSpec, structure: ChartStructure, t: TransitionRef): TransitionSpec {
  const node = t.state === null ? { on: chart.on } : stateAt(chart, pathOf(structure, t.state));
  const transitions = pathOfTrigger(t.trigger).reduce<unknown>(
    (value, key) => (value as Record<string, unknown>)[key],
    node,
  );
  return (transitions as readonly TransitionSpec[])[t.index] as TransitionSpec;
}
