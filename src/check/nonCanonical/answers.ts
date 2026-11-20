import type { Expression, Node } from "oxc-parser";
import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { Found } from "../../load/found.ts";
import { type LoadedSpec, placeIn } from "../../load/load.ts";
import { property, unwrap, visit } from "./ast.ts";

const results = ["accepted", "fulfilled", "rejected"] as const;

/** The answers that `node` passes to `answered(line, answers)` or to a peer's `answer(request, answer)`. */
function answersOf(node: Node): Expression[] {
  if (node.type !== "CallExpression") return [];
  const callee = unwrap(node.callee);
  const name =
    callee.type === "Identifier"
      ? callee.name
      : callee.type === "MemberExpression" && !callee.computed
        ? callee.property.name
        : undefined;
  const [, argument] = node.arguments;
  if ((name !== "answered" && name !== "answer") || argument === undefined || argument.type === "SpreadElement")
    return [];
  const answers = unwrap(argument);
  return answers.type === "ArrayExpression"
    ? answers.elements.flatMap((e) => (e === null || e.type === "SpreadElement" ? [] : [e]))
    : [answers];
}

export const check = (spec: LoadedSpec): Found<NonCanonical>[] =>
  spec.sources.flatMap((source) => {
    const found: Found<NonCanonical>[] = [];
    visit(source.program.body, (node) => {
      for (const answer of answersOf(node)) {
        const written = property(answer, "result");
        const value = written === undefined ? undefined : unwrap(written);
        const result = results.find((r) => value?.type === "Literal" && value.value === r);
        if (result !== undefined)
          found.push({
            violation: { kind: "NonCanonical.answerLiteral", definition: null, data: { result } },
            place: placeIn(source, answer.start),
          });
      }
    });
    return found;
  });
