import type { DefinitionRef } from "../../data/definitionRef.ts";
import type { NonCanonical } from "../../data/nonCanonical.ts";
import { stateAt, transitionAt } from "../../dsl/chart.ts";
import type { ChartSpec } from "../../dsl/definition.ts";
import {
  type ChartStructure,
  isAnswerTransition,
  type TransitionStructure,
  transitionRef,
} from "../../spec/structure.ts";
import { isDescendant } from "../../spec/tree.ts";
import type { Found } from "../found.ts";
import { charts, type Spec } from "../load.ts";

const isEmpty = (value: object | undefined) => value !== undefined && Object.keys(value).length === 0;

function emptyKeywords(chart: ChartSpec, structure: ChartStructure, definition: DefinitionRef): NonCanonical[] {
  const guards = (transitions: readonly TransitionStructure[]): NonCanonical[] =>
    transitions
      .filter((t) => isEmpty(transitionAt(chart, structure, transitionRef(t)).guard))
      .map((t) => ({ kind: "NonCanonical.emptyGuard", definition, data: { transition: transitionRef(t) } }));
  return [
    ...guards(structure.on),
    ...structure.states.flatMap((state) => {
      const after: NonCanonical[] = isEmpty(stateAt(chart, state.path).after)
        ? [{ kind: "NonCanonical.emptyAfter", definition, data: { state: state.name } }]
        : [];
      return [...after, ...guards(state.transitions)];
    }),
  ];
}

// Like ESLint's prefer-const, this reports a definition that does not need its more general form.
function statelessMachine(chart: ChartStructure, definition: DefinitionRef): NonCanonical[] {
  if (chart.kind !== "machine") return [];
  const waits = chart.states.some(
    (s) =>
      s.deadlines.length > 0 ||
      s.activities.some((a) => a.keyword === "calls") ||
      s.transitions.some(isAnswerTransition),
  );
  const oneToOne =
    Object.keys(chart.receives).length === 1 &&
    Object.keys(chart.commands).length === 1 &&
    Object.keys(chart.queries).length === 0;
  if (!oneToOne || chart.states.length > 1 || chart.context.length > 0 || waits) return [];
  return [{ kind: "NonCanonical.statelessMachine", definition, data: {} }];
}

// SCXML defaults a transition to the state itself or a descendant to external, and XState v5 defaults it to
// `reenter: false`. The defaults disagree, so the spec states it.
function reenters(chart: ChartStructure, definition: DefinitionRef): NonCanonical[] {
  const withinSource = ({ source, target }: TransitionStructure) =>
    source !== null && target !== null && isDescendant(chart, target, source);
  return [chart.on, ...chart.states.map((s) => s.transitions)]
    .flat()
    .filter((t) => (t.reenter !== null) !== withinSource(t))
    .map((t) => ({
      kind:
        t.reenter === null
          ? "NonCanonical.missingReenter"
          : t.source === null
            ? "NonCanonical.reenterOnRoot"
            : "NonCanonical.reenterOutsideSource",
      definition,
      data: { transition: transitionRef(t) },
    }));
}

export const check = (spec: Spec): Found<NonCanonical>[] =>
  charts(spec).flatMap(({ named, chart, structure }) => {
    const definition = { service: named.service, name: named.name };
    return [
      ...emptyKeywords(chart, structure, definition),
      ...statelessMachine(structure, definition),
      ...reenters(structure, definition),
    ].map((violation) => ({ violation, place: named.place }));
  });
