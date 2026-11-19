import type { Expression } from "oxc-parser";
import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { Found } from "../../load/found.ts";
import { placeIn, type Spec } from "../../load/load.ts";
import { keyName, unwrap } from "./ast.ts";

const DURATION_UNITS = new Set(["years", "months", "weeks", "days", "hours", "minutes", "seconds", "milliseconds"]);

function isConstantLiteral(node: Expression | null): boolean {
  if (node === null) return false;
  const e = unwrap(node);
  switch (e.type) {
    case "Literal":
      return ["number", "string", "boolean", "bigint"].includes(typeof e.value);
    case "UnaryExpression":
      return e.operator === "-" && isConstantLiteral(e.argument);
    case "TemplateLiteral":
      return e.expressions.length === 0;
    case "ArrayExpression":
      return (
        e.elements.length > 0 &&
        e.elements.every((x) => x !== null && x.type !== "SpreadElement" && isConstantLiteral(x))
      );
    case "ObjectExpression":
      return (
        e.properties.length > 0 &&
        e.properties.every(
          (p) => p.type === "Property" && DURATION_UNITS.has(keyName(p) ?? "") && isConstantLiteral(p.value),
        )
      );
    default:
      return false;
  }
}

export const check = (spec: Spec): Found<NonCanonical>[] =>
  spec.sources.flatMap((source) =>
    source.program.body.flatMap((statement) => {
      if (statement.type !== "ExportNamedDeclaration" || statement.declaration?.type !== "VariableDeclaration")
        return [];
      return statement.declaration.declarations.flatMap((d): Found<NonCanonical>[] =>
        d.id.type === "Identifier" && isConstantLiteral(d.init)
          ? [
              {
                violation: { kind: "NonCanonical.ungroupedConstant", definition: null, data: { name: d.id.name } },
                place: placeIn(source, d.id.start),
              },
            ]
          : [],
      );
    }),
  );
