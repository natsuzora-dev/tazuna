import type { DefinitionRef } from "../../data/definitionRef.ts";
import {
  type ActivityStructure,
  type ChartStructure,
  type StateStructure,
  schemaProperties,
  type TransitionStructure,
  traceNameOfRef,
} from "../../syntax/structure.ts";

/**
 * A transition of a chart. `source` is the declaring state, or null for the chart's own `on`. `source`, `keys`, and
 * `index` locate the guard and assign that Functions evaluates. An unguarded transition holds without asking Functions.
 */
export interface Transition {
  readonly source: string | null;
  readonly keys: readonly string[];
  readonly index: number;
  readonly target: string | null;
  readonly guarded: boolean;
  readonly reenter: boolean;
}

/**
 * A request that a state sends or a screen that it opens. `target` is the trace name, as seen from the service, of the
 * receiving definition (the opened screen for opens), and `service` and `name` identify it. `own` marks an own-service
 * command, which the internal queue processes without trace lines. `modal` marks an opened screen that blocks
 * operations on other screens while it is open.
 */
export interface Activity {
  readonly keyword: "calls" | "sends" | "shows" | "opens";
  readonly key: string;
  readonly target: string;
  readonly service: string;
  readonly name: string;
  readonly own: boolean;
  readonly modal: boolean;
}

export const activityRef = (a: Activity): DefinitionRef => ({ service: a.service, name: a.name });

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
  /** Each receives key and the trace name of its received event. */
  readonly receives: readonly (readonly [string, string])[];
  readonly screen: boolean;
  /** Whether another screen's opens opens the chart. */
  readonly opened: boolean;
  readonly offers: StateStructure["offers"];
  readonly controls: readonly Control[];
}

const sameKeys = (a: readonly string[], b: readonly string[]) =>
  a.length === b.length && a.every((key, i) => key === b[i]);

export function transitionsAt(c: Chart, source: string | null, keys: readonly string[]): readonly Transition[] {
  return (source === null ? c.on : (c.states.get(source)?.transitions ?? [])).filter((t) => sameKeys(t.keys, keys));
}

function transitionOf(t: TransitionStructure): Transition {
  return {
    source: t.source,
    keys: t.keys,
    index: t.index,
    target: t.target,
    guarded: t.guards.length > 0,
    reenter: t.reenter === true,
  };
}

/** Returns the activity of `a`, or none when it names no definition. */
function activityOf(service: string, a: ActivityStructure): Activity[] {
  const r = a.definition;
  if (r === null) return [];
  return [
    {
      keyword: a.keyword,
      key: a.name,
      target: traceNameOfRef(r, service),
      service: r.service,
      name: r.name,
      own: a.keyword === "sends" && r.service === service,
      modal: a.keyword === "opens" && a.modal,
    },
  ];
}

/** Returns the executable chart of the structure `c` of `service`, dropping each receives key that names no event. */
export function executableChart(c: ChartStructure, service: string, order: number, opened: boolean): Chart {
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
          activities: st.activities.flatMap((a) => activityOf(service, a)),
          transitions: st.transitions.map(transitionOf),
          offers: st.offers,
        },
      ]),
    ),
    tree: c,
    receives: Object.entries(c.receives).flatMap(([key, r]) =>
      r === null ? [] : [[key, traceNameOfRef(r, service)] as const],
    ),
    screen: c.kind === "screen",
    opened,
    offers: c.offers,
    controls: Object.entries(c.controls).map(([name, payload]) => ({
      name,
      hasPayload: schemaProperties(payload).length > 0,
    })),
  };
}
