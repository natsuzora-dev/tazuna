import { describe } from "node:test";
import { depth, groupExamples } from "./examples.ts";
import { testExamples } from "./expected.ts";

describe("Uncovered examples", () => {
  const examples = groupExamples("explore", "uncovered");

  testExamples(examples, "Uncovered", ["test", ".", "--depth", String(depth), "--coverage"]);
});
