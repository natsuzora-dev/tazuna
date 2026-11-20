import assert from "node:assert/strict";
import { describe, test } from "node:test";
import { collisionProbability, Visited } from "../src/explore/search.ts";
import { depth, groupExamples } from "./examples.ts";
import { testExamples } from "./expected.ts";

describe("Uncovered examples", () => {
  const examples = groupExamples("explore", "uncovered");

  testExamples(examples, "Uncovered", ["test", ".", "--depth", String(depth), "--coverage"]);
});

test("the visited set takes a fingerprint as visited only once it was added", () => {
  const visited = new Visited();
  assert.deepEqual(
    ["a", "b", "a", "ab"].map((f) => visited.add(f)),
    [true, true, false, true],
  );
  assert.equal(visited.size, 3);
});

test("the collision probability is about n^2/2^65 summed over the visited sets", () => {
  assert.equal(collisionProbability([1]), 0);
  assert.equal(collisionProbability([1e6]).toPrecision(2), "2.7e-8");
  assert.equal(collisionProbability([1e6, 1e6]).toPrecision(2), "5.4e-8");
});
