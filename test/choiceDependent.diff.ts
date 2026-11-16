import assert from "node:assert/strict";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { type DecidedOrder, stepOrderChanges } from "../src/explore/stepOrders.ts";
import { loadSpec } from "../src/load/load.ts";
import { stepOrderLimit } from "../src/observe/choiceDependent.ts";
import { simulateSpec } from "../src/sim/spec/simulate.ts";
import { runExamples, runGroupExamples } from "./examples.ts";
import { SimFunctions, VerifyFunctions } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const tests = import.meta.dirname;

const lean = new Lean();
after(() => lean.close());

const relationExamples = new Set(runGroupExamples("choiceDependent"));

const simRoots = [join(tests, "../samples/todo/spec"), ...runExamples()];

// Every spec loads before any test runs, so that no test ends while a later one is still being registered.
const simCases = await Promise.all(
  simRoots.map(async (root) => {
    const spec = await loadSpec(root);
    const decided: DecidedOrder[] = [];
    for (const { definition } of spec.scenarios)
      stepOrderChanges(spec, definition.scenario, simulateSpec(spec, definition.scenario), 0, (d) => decided.push(d));
    return { root, spec, decided };
  }),
);

for (const { root, spec, decided } of simCases) {
  if (spec.scenarios.length === 0 || (decided.length === 0 && !relationExamples.has(root))) continue;
  test(`${relative(tests, root)}: TS and Lean find the same ChoiceDependent violation for each step order that the search runs`, (t) => {
    assert.ok(decided.length > 0, "the search runs step orders in each example of a ChoiceDependent violation");
    let found = 0;
    for (const { scenario, origin, service, order, found: ts } of decided) {
      const functions = new SimFunctions(spec, (part) => lean.read(part));
      const verify = new VerifyFunctions(spec);
      const fromLean = lean.stepOrder(spec, scenario, origin, service, order, {
        answer: (message) => (message["type"] === "comparableValue" ? verify : functions).answer(message),
      });
      const expected = ts === undefined ? null : JSON.parse(JSON.stringify(ts));
      assert.deepEqual(fromLean, expected, `${service} at ${JSON.stringify(origin)} with ${JSON.stringify(order)}`);
      if (ts !== undefined) found += 1;
    }
    t.diagnostic(`${decided.length} orders, ${found} findings`);
  });
}

test("stepOrderLimit is Lean's", () => {
  assert.equal(stepOrderLimit, lean.names().stepOrderLimit);
});
