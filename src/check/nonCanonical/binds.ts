import type { Expression } from "oxc-parser";
import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { AnyCommand, Automation } from "../../dsl/definition.ts";
import type { Found } from "../../load/found.ts";
import { placeIn, type Spec } from "../../load/load.ts";
import { keyName, unwrap, visit, writtenOf } from "./ast.ts";

const isBound = (n: Expression) => n.type === "Identifier" && n.name === "bound";

function boundReads(init: Expression): Set<string> | "all" {
  const reads = new Set<string>();
  let all = false;
  visit(init, (n) => {
    if (n.type === "MemberExpression" && !n.computed && isBound(unwrap(n.object))) reads.add(n.property.name);
    if (n.type === "Property" && keyName(n) === "bound" && n.value.type === "ObjectPattern")
      for (const p of n.value.properties) {
        const name = p.type === "Property" ? keyName(p) : undefined;
        if (name !== undefined) reads.add(name);
      }
    if (n.type === "CallExpression" && n.arguments.some((a) => a.type !== "SpreadElement" && isBound(unwrap(a))))
      all = true;
  });
  return all ? "all" : reads;
}

export const check = (spec: Spec): Found<NonCanonical>[] =>
  writtenOf(spec).flatMap(({ source, definition: d, init }) => {
    if (d === null || (d.definition.kind !== "automation" && d.definition.kind !== "command")) return [];
    const names = Object.keys((d.definition as Automation | AnyCommand).binds);
    const reads = names.length === 0 ? "all" : boundReads(init);
    if (reads === "all") return [];
    const definition = { service: d.service, name: d.name };
    return names
      .filter((name) => !reads.has(name))
      .map((binding) => ({
        violation: { kind: "NonCanonical.unreadBinding", definition, data: { binding } },
        place: placeIn(source, init.start),
      }));
  });
