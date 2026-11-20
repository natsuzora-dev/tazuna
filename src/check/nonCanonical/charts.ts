import type { DefinitionRef } from "../../data/definitionRef.ts";
import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { Found } from "../../load/found.ts";
import { charts, type Spec } from "../../load/load.ts";
import {
  type ChartStructure,
  isAnswerTransition,
  schemaProperties,
  type TransitionStructure,
  transitionRef,
} from "../../spec/structure.ts";
import { isDescendant } from "../../spec/tree.ts";

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
  if (!oneToOne || chart.states.length > 1 || schemaProperties(chart.context).length > 0 || waits) return [];
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
  charts(spec).flatMap(({ named, structure }) => {
    const definition = { service: named.service, name: named.name };
    return [...statelessMachine(structure, definition), ...reenters(structure, definition)].map((violation) => ({
      violation,
      place: named.place,
    }));
  });
