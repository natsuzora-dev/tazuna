import type { NonCanonical } from "../../data/nonCanonical.ts";
import { stateAt } from "../../dsl/chart.ts";
import type { Automation } from "../../dsl/definition.ts";
import type { Found } from "../../load/found.ts";
import { charts, type Spec } from "../../load/load.ts";
import { rejectionKinds } from "../../spec/structure.ts";

const kindOf = (arrives: boolean) =>
  arrives ? "NonCanonical.missingOnRejected" : "NonCanonical.unreachableOnRejected";

/**
 * An automation ignores an unavailable rejection with `onRejected: []`; every other kind is a fault of the automation.
 */
const automations = (spec: Spec): Found<NonCanonical>[] =>
  spec.structure.definitions.flatMap((d): Found<NonCanonical>[] => {
    if (d.kind !== "automation" || d.command === null) return [];
    const named = spec.definitions.find((n) => n.service === d.service && n.name === d.name);
    if (named === undefined) return [];
    const arrives = rejectionKinds(spec.structure, d.service, d.command).includes("unavailable");
    const written = (named.definition as Automation).onRejected !== undefined;
    if (arrives === written) return [];
    return [
      {
        violation: { kind: kindOf(arrives), definition: { service: d.service, name: d.name }, data: {} },
        place: named.place,
      },
    ];
  });

/** A state that calls or sends writes `onRejected` exactly when an answer may be rejected. */
const states = (spec: Spec): Found<NonCanonical>[] =>
  charts(spec).flatMap(({ named, chart, structure }) =>
    structure.states.flatMap((state) =>
      state.activities.flatMap((a): Found<NonCanonical>[] => {
        if ((a.keyword !== "calls" && a.keyword !== "sends") || a.definition === null) return [];
        const arrives = rejectionKinds(spec.structure, named.service, a.definition).length > 0;
        const written = stateAt(chart, state.path)[a.keyword]?.[a.name]?.onRejected !== undefined;
        if (arrives === written) return [];
        const definition = { service: named.service, name: named.name };
        const data = { state: state.name, keys: [a.keyword, a.name, "onRejected"] };
        return [{ violation: { kind: kindOf(arrives), definition, data }, place: named.place }];
      }),
    ),
  );

export const check = (spec: Spec): Found<NonCanonical>[] => [...automations(spec), ...states(spec)];
