import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { Found } from "../../load/found.ts";
import { charts, type Spec, structured } from "../../load/load.ts";
import { rejectionKinds } from "../../spec/structure.ts";

const kindOf = (arrives: boolean) =>
  arrives ? "NonCanonical.missingOnRejected" : "NonCanonical.unreachableOnRejected";

/**
 * An automation ignores an unavailable rejection with `onRejected: []`; every other kind is a fault of the automation.
 */
const automations = (spec: Spec): Found<NonCanonical>[] =>
  structured(spec).flatMap(({ named, structure: d }): Found<NonCanonical>[] => {
    if (d.kind !== "automation") return [];
    const arrives = rejectionKinds(spec.structure, d.service, d.command).includes("unavailable");
    if (arrives === d.onRejected) return [];
    return [
      {
        violation: { kind: kindOf(arrives), definition: { service: d.service, name: d.name }, data: {} },
        place: named.place,
      },
    ];
  });

/** A state that calls or sends writes `onRejected` exactly when an answer may be rejected. */
const states = (spec: Spec): Found<NonCanonical>[] =>
  charts(spec).flatMap(({ named, structure }) =>
    structure.states.flatMap((state) =>
      state.activities.flatMap((a): Found<NonCanonical>[] => {
        if (a.keyword !== "calls" && a.keyword !== "sends") return [];
        const arrives = rejectionKinds(spec.structure, named.service, a.definition).length > 0;
        if (arrives === a.onRejected) return [];
        const definition = { service: named.service, name: named.name };
        const data = { state: state.name, trigger: { type: a.keyword, key: a.name, outcome: "onRejected" } as const };
        return [{ violation: { kind: kindOf(arrives), definition, data }, place: named.place }];
      }),
    ),
  );

export const check = (spec: Spec): Found<NonCanonical>[] => [...automations(spec), ...states(spec)];
