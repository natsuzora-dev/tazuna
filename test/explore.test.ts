import { describe } from "node:test";
import { depth, groupExamples } from "./examples.ts";
import { testEveryKind, testExamples } from "./expected.ts";
import { uncoveredKinds } from "./kinds.ts";

describe("Uncovered examples", () => {
  const examples = groupExamples("explore", "uncovered");

  testExamples(examples, "Uncovered", ["test", ".", "--depth", String(depth), "--coverage"]);

  testEveryKind(examples, Object.keys(uncoveredKinds));
});
