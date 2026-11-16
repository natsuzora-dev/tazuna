import { type Obligation, type Uncovered, uncovered } from "../../data/uncovered.ts";
import type { Found } from "../../load/found.ts";
import { type Spec, structured } from "../../load/load.ts";
import type { Coverage } from "../../sim/spec/coverage.ts";

type Outcomes = readonly [passed: Obligation, failed: Obligation];

export const check = (spec: Spec, reached: Coverage): Found<Uncovered>[] =>
  structured(spec).flatMap(({ named, structure: d }) => {
    if (d.kind !== "automation") return [];
    const definition = { service: d.service, name: d.name };
    const automation: Obligation = { kind: "automation", definition, data: {} };
    const chain: Outcomes[] = [];
    for (const binding of d.binds)
      chain.push([
        { kind: "automationBindingValue", definition, data: { binding } },
        { kind: "automationBindingNull", definition, data: { binding } },
      ]);
    for (const condition of d.guard)
      chain.push([
        { kind: "automationGuard", definition, data: { condition, met: true } },
        { kind: "automationGuard", definition, data: { condition, met: false } },
      ]);
    const outcomes = chain
      .filter((_, k) => {
        const previous = chain[k - 1]?.[0];
        return previous === undefined || reached.has(previous);
      })
      .flat();
    return (reached.has(automation) ? outcomes : [automation])
      .filter((o) => !reached.has(o))
      .map((o) => ({ violation: uncovered(o), place: named.place }));
  });
