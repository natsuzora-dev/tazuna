import { type Obligation, type Uncovered, uncovered } from "../../data/uncovered.ts";
import type { Found } from "../../load/found.ts";
import { type Spec, structured } from "../../load/load.ts";
import type { Coverage } from "../../sim/spec/coverage.ts";

export const check = (spec: Spec, reached: Coverage): Found<Uncovered>[] =>
  structured(spec).flatMap(({ named, structure: d }) => {
    if (d.kind !== "command" && d.kind !== "query") return [];
    const definition = { service: d.service, name: d.name };
    const request: Obligation = { kind: "request", definition, data: {} };
    const answers: Obligation[] = [];
    if (d.rejects === null) {
      answers.push({ kind: "successAnswer", definition, data: {} });
      for (const binding of d.kind === "command" ? d.binds : [])
        answers.push({ kind: "bindsRejection", definition, data: { binding } });
      for (const condition of d.requires) answers.push({ kind: "requiresRejection", definition, data: { condition } });
    }
    return (reached.has(request) ? answers : [request])
      .filter((o) => !reached.has(o))
      .map((o) => ({ violation: uncovered(o), place: named.place }));
  });
