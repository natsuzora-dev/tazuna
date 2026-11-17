import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { Found } from "../../load/found.ts";
import { placeIn, type Spec } from "../../load/load.ts";

const DURATION_UNITS = new Set(["years", "months", "weeks", "days", "hours", "minutes", "seconds", "milliseconds"]);

interface Node {
  readonly type: string;
  readonly value?: unknown;
  readonly operator?: string;
  readonly argument?: Node;
  readonly expression?: Node;
  readonly expressions?: readonly Node[];
  readonly elements?: readonly (Node | null)[];
  readonly properties?: readonly (Node & { readonly key?: Node & { readonly name?: string } })[];
}

function isConstantLiteral(node: Node | null | undefined): boolean {
  if (node === null || node === undefined) return false;
  switch (node.type) {
    case "TSAsExpression":
    case "TSSatisfiesExpression":
      return isConstantLiteral(node.expression);
    case "Literal":
      return ["number", "string", "boolean", "bigint"].includes(typeof node.value);
    case "UnaryExpression":
      return node.operator === "-" && isConstantLiteral(node.argument);
    case "TemplateLiteral":
      return node.expressions?.length === 0;
    case "ArrayExpression":
      return (node.elements ?? []).length > 0 && (node.elements ?? []).every(isConstantLiteral);
    case "ObjectExpression":
      return (
        (node.properties ?? []).length > 0 &&
        (node.properties ?? []).every(
          (p) => p.type === "Property" && DURATION_UNITS.has(p.key?.name ?? "") && isConstantLiteral(p.value as Node),
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
        d.id.type === "Identifier" && isConstantLiteral(d.init as Node | null)
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
