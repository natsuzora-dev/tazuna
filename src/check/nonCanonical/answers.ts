import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { Found } from "../../load/found.ts";
import { placeIn, type Spec } from "../../load/load.ts";

interface Node {
  readonly type?: string;
  readonly start?: number;
  readonly value?: unknown;
  readonly key?: { readonly type?: string; readonly name?: string; readonly value?: unknown };
  readonly properties?: readonly Node[];
}

/** The key that an answer with the result `result` has next to `result`, which its constructor takes. */
const detail = { accepted: null, fulfilled: "output", rejected: "rejection" } as const;
type Result = keyof typeof detail;

const keyName = (p: Node) => (p.key?.type === "Identifier" ? p.key.name : p.key?.value);

/** The result of an answer written as an object literal that `accepted`, `fulfilled`, or `rejected` writes. */
function literalResult(node: Node): Result | undefined {
  if (node.type !== "ObjectExpression") return undefined;
  const properties = node.properties ?? [];
  if (properties.some((p) => p.type !== "Property")) return undefined;
  const result = properties.find((p) => keyName(p) === "result")?.value as Node | undefined;
  const value = result?.type === "Literal" ? result.value : undefined;
  if (value !== "accepted" && value !== "fulfilled" && value !== "rejected") return undefined;
  const other = detail[value];
  const keys = properties.map(keyName).sort();
  const expected = other === null ? ["result"] : [other, "result"].sort();
  return keys.length === expected.length && keys.every((k, i) => k === expected[i]) ? value : undefined;
}

export const check = (spec: Spec): Found<NonCanonical>[] =>
  spec.sources.flatMap((source) => {
    const found: Found<NonCanonical>[] = [];
    const visit = (node: unknown): void => {
      if (node === null || typeof node !== "object") return;
      if (Array.isArray(node)) {
        for (const child of node) visit(child);
        return;
      }
      const result = literalResult(node as Node);
      if (result !== undefined)
        found.push({
          violation: { kind: "NonCanonical.answerLiteral", definition: null, data: { result } },
          place: placeIn(source, (node as Node).start ?? 0),
        });
      for (const value of Object.values(node)) visit(value);
    };
    visit(source.program.body);
    return found;
  });
