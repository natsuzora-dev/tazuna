import type { DefinitionRef } from "../data/definitionRef.ts";
import type { NonCanonical, OnRejectedAt } from "../data/nonCanonical.generated.ts";
import type { Trigger } from "../data/transitionRef.generated.ts";
import type { Structure } from "../spec/structure.generated.ts";
import {
  type ChartStructure,
  isAnswerTransition,
  rejectionKinds,
  schemaProperties,
  type TransitionStructure,
  transitionRef,
} from "../spec/structure.ts";
import { isDescendant } from "../spec/tree.ts";

const charts = (structure: Structure) =>
  structure.definitions.filter((d): d is ChartStructure => d.kind === "machine" || d.kind === "screen");

// Like ESLint's prefer-const, this reports a definition that does not need its more general form.
function statelessMachines(structure: Structure): NonCanonical[] {
  return charts(structure).flatMap((chart): NonCanonical[] => {
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
    return [
      { kind: "NonCanonical.statelessMachine", definition: { service: chart.service, name: chart.name }, data: {} },
    ];
  });
}

// SCXML defaults a transition to the state itself or a descendant to external, and XState v5 defaults it to
// `reenter: false`. The defaults disagree, so the spec states it.
function reenters(structure: Structure): NonCanonical[] {
  return charts(structure).flatMap((chart) => {
    const definition = { service: chart.service, name: chart.name };
    const withinSource = ({ source, target }: TransitionStructure) =>
      source !== null && target !== null && isDescendant(chart, target, source);
    return [chart.on, ...chart.states.map((s) => s.transitions)]
      .flat()
      .filter((t) => (t.reenter !== null) !== withinSource(t))
      .map(
        (t): NonCanonical => ({
          kind:
            t.reenter === null
              ? "NonCanonical.missingReenter"
              : t.source === null
                ? "NonCanonical.reenterOnRoot"
                : "NonCanonical.reenterOutsideSource",
          definition,
          data: { transition: transitionRef(t) },
        }),
      );
  });
}

const onRejected = (definition: DefinitionRef, arrives: boolean, at: OnRejectedAt): NonCanonical => ({
  kind: arrives ? "NonCanonical.missingOnRejected" : "NonCanonical.unreachableOnRejected",
  definition,
  data: { at },
});

/** An automation ignores an unavailable rejection with `onRejected: []`; every other kind is a fault of the automation. */
const automations = (structure: Structure): NonCanonical[] =>
  structure.definitions.flatMap((d): NonCanonical[] => {
    if (d.kind !== "automation") return [];
    const arrives = rejectionKinds(structure, d.service, d.command).includes("unavailable");
    return arrives === d.onRejected
      ? []
      : [onRejected({ service: d.service, name: d.name }, arrives, { kind: "automation" })];
  });

/** A state that calls or sends writes `onRejected` exactly when an answer may be rejected. */
const states = (structure: Structure): NonCanonical[] =>
  charts(structure).flatMap((chart) =>
    chart.states.flatMap((state) =>
      state.activities.flatMap((a): NonCanonical[] => {
        if (a.keyword !== "calls" && a.keyword !== "sends") return [];
        const arrives = rejectionKinds(structure, chart.service, a.definition).length > 0;
        if (arrives === a.onRejected) return [];
        const trigger: Trigger = { type: a.keyword, key: a.name, outcome: "onRejected" };
        const at: OnRejectedAt = { kind: "request", state: state.name, trigger };
        return [onRejected({ service: chart.service, name: chart.name }, arrives, at)];
      }),
    ),
  );

/** Lean's Canonical.check: the NonCanonical violations that the structure shows. */
export const check = (structure: Structure): NonCanonical[] => [
  ...statelessMachines(structure),
  ...reenters(structure),
  ...automations(structure),
  ...states(structure),
];
