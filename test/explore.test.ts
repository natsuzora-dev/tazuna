import { describe } from "node:test";
import { kindsOf } from "../src/data/kinds.ts";
import { depth, groupExamples } from "./examples.ts";
import { testEveryKind, testExamples } from "./expected.ts";

describe("Uncovered examples", () => {
  const examples = groupExamples("explore", "uncovered");

  testExamples(examples, "Uncovered", ["test", ".", "--depth", String(depth), "--coverage"]);

  testEveryKind(examples, kindsOf.Uncovered);
});
