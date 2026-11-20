import type { DefinitionRef } from "../data/definitionRef.ts";
import { type Obligation, type Uncovered, uncovered } from "../data/uncovered.ts";
import type { Coverage } from "../sim/spec/coverage.ts";
import type { Definition, Structure, Transition } from "../spec/structure.generated.ts";
import { transitionRef } from "../spec/structure.ts";

const refOf = (d: Definition): DefinitionRef => ({ service: d.service, name: d.name });

/** Lean's requestsUncovered. */
function requestsUncovered(reached: Coverage, d: Definition): Obligation[] {
  if (d.kind !== "command" && d.kind !== "query") return [];
  const definition = refOf(d);
  const request: Obligation = { kind: "request", definition, data: {} };
  const answers: Obligation[] =
    d.rejects !== null
      ? []
      : [
          { kind: "successAnswer", definition, data: {} },
          ...(d.kind === "command" ? d.binds : []).map(
            (binding): Obligation => ({ kind: "bindsRejection", definition, data: { binding } }),
          ),
          ...d.requires.map(
            (condition): Obligation => ({ kind: "requiresRejection", definition, data: { condition } }),
          ),
        ];
  return (reached.has(request) ? answers : [request]).filter((o) => !reached.has(o));
}

/** Lean's automationUncovered. */
function automationUncovered(reached: Coverage, d: Definition): Obligation[] {
  if (d.kind !== "automation") return [];
  const definition = refOf(d);
  const chain: (readonly [Obligation, Obligation])[] = [
    ...d.binds.map(
      (binding) =>
        [
          { kind: "automationBindingValue", definition, data: { binding } },
          { kind: "automationBindingNull", definition, data: { binding } },
        ] as const,
    ),
    ...d.guard.map(
      (condition) =>
        [
          { kind: "automationGuard", definition, data: { condition, met: true } },
          { kind: "automationGuard", definition, data: { condition, met: false } },
        ] as const,
    ),
  ];
  const outcomes = chain.filter((_, k) => k === 0 || reached.has((chain[k - 1] as (typeof chain)[number])[0])).flat();
  const automation: Obligation = { kind: "automation", definition, data: {} };
  return (reached.has(automation) ? outcomes : [automation]).filter((o) => !reached.has(o));
}

/** Lean's chartUncovered. */
function chartUncovered(reached: Coverage, d: Definition): Obligation[] {
  if (d.kind !== "machine" && d.kind !== "screen") return [];
  const definition = refOf(d);
  const entered = (state: string) => reached.has({ kind: "state", definition, data: { state } });
  const started = entered(d.initial);
  const transitions = (all: readonly Transition[]): Obligation[] =>
    all.flatMap((t) => {
      const transition = transitionRef(t);
      return [
        { kind: "transition", definition, data: { transition } },
        ...t.guards.map(
          (condition): Obligation => ({ kind: "guardFalse", definition, data: { transition, condition } }),
        ),
      ];
    });
  const states = d.states.flatMap((state): Obligation[] => {
    const parentEntered = state.parent === null ? started || state.name === d.initial : entered(state.parent);
    return [
      ...(state.kind === "history" || !parentEntered
        ? []
        : [{ kind: "state", definition, data: { state: state.name } } as const]),
      ...(entered(state.name) ? transitions(state.transitions) : []),
    ];
  });
  return [...(started ? transitions(d.on) : []), ...states].filter((o) => !reached.has(o));
}

/** Lean's uncovered: what `test --coverage` reports, by definition: requests, then automations, then charts. */
export const uncoveredParts = (structure: Structure, reached: Coverage): Uncovered[] =>
  [requestsUncovered, automationUncovered, chartUncovered]
    .flatMap((check) => structure.definitions.flatMap((d) => check(reached, d)))
    .map(uncovered);
