import type { NonCanonical } from "../../data/nonCanonical.ts";
import { pathOfTrigger, transitionArrays } from "../../dsl/chart.ts";
import type { StateSpec } from "../../dsl/definition.ts";
import { writtenOptions } from "../../dsl/written.ts";
import type { Found } from "../../load/found.ts";
import type { Spec } from "../../load/load.ts";

type Path = readonly (string | number)[];
type Written = Readonly<Record<string, unknown>>;

const isEmpty = (value: unknown): boolean =>
  typeof value === "object" &&
  value !== null &&
  Object.getPrototypeOf(value) === Object.prototype &&
  Object.keys(value).length === 0;

const entries = (object: unknown): [string, Written][] =>
  typeof object === "object" && object !== null ? (Object.entries(object) as [string, Written][]) : [];

/** The paths of the keys of `object` whose value is `{}`. */
const emptyIn = (object: unknown, at: Path): Path[] =>
  entries(object)
    .filter(([, value]) => isEmpty(value))
    .map(([key]) => [...at, key]);

const transitions = (node: Written, at: Path): Path[] =>
  transitionArrays(node as StateSpec).flatMap(({ trigger, transitions }) =>
    transitions.flatMap((t, i) => emptyIn(t, [...at, ...pathOfTrigger(trigger), i])),
  );

const tree = (states: unknown, at: Path): Path[] =>
  entries(states).flatMap(([name, node]) => [
    ...emptyIn(node, [...at, name]).filter((path) => path.at(-1) !== "key"),
    ...tree(node["states"], [...at, name, "states"]),
  ]);

const behaviors = (chart: Written): Path[] => [
  ...emptyIn(chart["states"], ["states"]),
  ...transitions({ on: chart["on"] ?? {} }, []),
  ...entries(chart["states"]).flatMap(([name, row]) => {
    const at = ["states", name];
    return [
      ...emptyIn(row, at),
      ...emptyIn(row["entry"], [...at, "entry"]),
      ...emptyIn(row["exit"], [...at, "exit"]),
      ...transitions(row, at),
    ];
  }),
];

/** The paths of the keywords written as `{}` in `options`, the objects written to the calls that made a definition. */
function emptyKeywords(options: readonly Written[], charted: boolean): Path[] {
  const [setup, chart] = options;
  return [
    ...options.flatMap((o) => emptyIn(o, [])),
    ...(charted && setup !== undefined && chart !== undefined
      ? [
          ...tree(setup["states"], ["states"]),
          ...entries(setup["controls"]).flatMap(([name, c]) => emptyIn(c, ["controls", name])),
          ...behaviors(chart),
        ]
      : []),
  ];
}

export const check = (spec: Spec): Found<NonCanonical>[] => [
  ...[...spec.services].flatMap(([service, s]) =>
    emptyKeywords(writtenOptions(s.definition) as readonly Written[], false).map(
      (path): Found<NonCanonical> => ({
        violation: { kind: "NonCanonical.emptyKeyword", definition: null, data: { service, path } },
        place: s.place,
      }),
    ),
  ),
  ...spec.definitions.flatMap((d) => {
    const charted = d.definition.kind === "machine" || d.definition.kind === "screen";
    return emptyKeywords(writtenOptions(d.definition) as readonly Written[], charted).map(
      (path): Found<NonCanonical> => ({
        violation: {
          kind: "NonCanonical.emptyKeyword",
          definition: { service: d.service, name: d.name },
          data: { path },
        },
        place: d.place,
      }),
    );
  }),
];
