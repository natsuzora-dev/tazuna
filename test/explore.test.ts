import { describe } from "node:test";
import type { Uncovered } from "../src/data/uncovered.ts";
import { depth, groupExamples } from "./examples.ts";
import { testEveryKind, testExamples } from "./expected.ts";

describe("Uncovered examples", () => {
  const examples = groupExamples("explore", "uncovered");

  testExamples(examples, "Uncovered", ["test", ".", "--depth", String(depth), "--coverage"]);

  const kinds: Readonly<Record<Uncovered["kind"], true>> = {
    "Uncovered.request": true,
    "Uncovered.successAnswer": true,
    "Uncovered.bindsRejection": true,
    "Uncovered.requiresRejection": true,
    "Uncovered.automation": true,
    "Uncovered.automationBindingValue": true,
    "Uncovered.automationBindingNull": true,
    "Uncovered.automationGuard": true,
    "Uncovered.transition": true,
    "Uncovered.guardFalse": true,
    "Uncovered.state": true,
  };

  testEveryKind(examples, Object.keys(kinds));
});
