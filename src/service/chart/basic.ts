import type { DefinitionRef } from "../../data/definitionRef.ts";
import type { Activity } from "../../data/step.generated.ts";
import type { Trigger } from "../../data/transitionRef.generated.ts";
import { sameJson } from "../../data/values.ts";
import {
  type ActivityStructure,
  type ChartStructure,
  type StateStructure,
  schemaProperties,
  type TransitionStructure,
} from "../../spec/structure.ts";

/**
 * A transition of a chart. `source` is the declaring state, or null for the chart's own `on`. `source`, `trigger`, and
 * `index` locate the guard and assign that Functions evaluates. An unguarded transition holds without asking Functions.
 */
export interface Transition {
  readonly source: string | null;
  readonly trigger: Trigger;
  readonly index: number;
  readonly target: string | null;
  readonly guarded: boolean;
  readonly reenter: boolean;
}

/** Whether `a` is an own-service command of `service`, which the internal queue processes without trace lines. */
export const isOwn = (a: Activity, service: string): boolean => a.keyword === "sends" && a.target.service === service;

/** The trigger of the transitions that take an answer to a calls or sends, rejected or not. */
export function answerTrigger(a: Activity, rejected: boolean): Trigger | undefined {
  if (a.keyword === "calls") return { type: "calls", key: a.key, outcome: rejected ? "onRejected" : "onFulfilled" };
  if (a.keyword === "sends") return { type: "sends", key: a.key, outcome: rejected ? "onRejected" : "onAccepted" };
  return undefined;
}

interface Control {
  readonly name: string;
  readonly hasPayload: boolean;
}

/** Lean's `path` and `children` have no field: TS reads them from the chart's structure, `tree`. */
interface ChartState {
  readonly name: string;
  readonly parent: string | null;
  readonly kind: StateStructure["kind"];
  readonly initial: string | null;
  /** The activities in the order calls, sends, shows, opens. */
  readonly activities: readonly Activity[];
  readonly transitions: readonly Transition[];
  readonly offers: StateStructure["offers"];
}

/** An executable chart. `tree` is the chart's structure, which the syntax tree functions read. */
export interface Chart {
  readonly name: string;
  /** The rank among the spec's definitions. Own-service commands are processed in sender-definition order. */
  readonly order: number;
  readonly initial: string;
  readonly on: readonly Transition[];
  /** The states by name, in document order. */
  readonly states: ReadonlyMap<string, ChartState>;
  readonly tree: ChartStructure;
  /** Each receives key and its received event. */
  readonly receives: readonly (readonly [string, DefinitionRef])[];
  readonly screen: boolean;
  /** Whether another screen's opens opens the chart. */
  readonly opened: boolean;
  readonly offers: StateStructure["offers"];
  readonly controls: readonly Control[];
}

export function transitionsAt(c: Chart, source: string | null, trigger: Trigger): readonly Transition[] {
  return (source === null ? c.on : (c.states.get(source)?.transitions ?? [])).filter((t) =>
    sameJson(t.trigger, trigger),
  );
}

function transitionOf(t: TransitionStructure): Transition {
  return {
    source: t.source,
    trigger: t.trigger,
    index: t.index,
    target: t.target,
    guarded: t.guards.length > 0,
    reenter: t.reenter === true,
  };
}

/** Returns the activity of `a`, or none when it names no definition. */
function activityOf(a: ActivityStructure): Activity[] {
  const target = a.definition;
  if (target === null) return [];
  return [
    a.keyword === "opens"
      ? { keyword: a.keyword, key: a.name, target, modal: a.modal }
      : { keyword: a.keyword, key: a.name, target },
  ];
}

/** Returns the executable chart of the structure `c`, dropping each receives key that names no event. */
export function executableChart(c: ChartStructure, order: number, opened: boolean): Chart {
  return {
    name: c.name,
    order,
    initial: c.initial,
    on: c.on.map(transitionOf),
    states: new Map(
      c.states.map((st) => [
        st.name,
        {
          name: st.name,
          parent: st.parent,
          kind: st.kind,
          initial: st.initial,
          activities: st.activities.flatMap(activityOf),
          transitions: st.transitions.map(transitionOf),
          offers: st.offers,
        },
      ]),
    ),
    tree: c,
    receives: Object.entries(c.receives).flatMap(([key, r]) => (r === null ? [] : [[key, r] as const])),
    screen: c.kind === "screen",
    opened,
    offers: c.offers,
    controls: Object.entries(c.controls).map(([name, payload]) => ({
      name,
      hasPayload: schemaProperties(payload).length > 0,
    })),
  };
}
