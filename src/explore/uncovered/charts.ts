import { type Obligation, type Uncovered, uncovered } from "../../data/uncovered.ts";
import type { Found } from "../../load/found.ts";
import { charts, type Spec } from "../../load/load.ts";
import type { Coverage } from "../../run/coverage.ts";
import { type TransitionStructure, transitionRef } from "../../syntax/structure.ts";

export const check = (spec: Spec, reached: Coverage): Found<Uncovered>[] =>
  charts(spec).flatMap(({ named, structure }) => {
    const definition = { service: named.service, name: named.name };
    const unreached = (o: Obligation): Uncovered[] => (reached.has(o) ? [] : [uncovered(o)]);
    const entered = (state: string) => reached.has({ kind: "state", definition, data: { state } });
    const started = entered(structure.initial);
    const transitions = (all: readonly TransitionStructure[]): Uncovered[] =>
      all.flatMap((t) => {
        const transition = transitionRef(t);
        return [
          ...unreached({ kind: "transition", definition, data: { transition } }),
          ...t.guards.flatMap((condition) =>
            unreached({ kind: "guardFalse", definition, data: { transition, condition } }),
          ),
        ];
      });
    const states = structure.states.flatMap((state) => {
      const parentEntered = state.parent === null ? started || state.name === structure.initial : entered(state.parent);
      return [
        ...(state.kind === "history" || !parentEntered
          ? []
          : unreached({ kind: "state", definition, data: { state: state.name } })),
        ...(entered(state.name) ? transitions(state.transitions) : []),
      ];
    });
    return [...(started ? transitions(structure.on) : []), ...states].map((violation) => ({
      violation,
      place: named.place,
    }));
  });
