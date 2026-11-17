import assert from "node:assert/strict";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { type AssignmentSearch, assignmentSearch } from "../src/explore/assignments.ts";
import { assignmentLimit, stepOrderLimit } from "../src/explore/choiceDependent.ts";
import { type Searched, stepOrderChanges } from "../src/explore/stepOrders.ts";
import { loadSpec } from "../src/load/load.ts";
import { simulateSpec } from "../src/sim/spec/simulate.ts";
import { runExamples, runGroupExamples } from "./examples.ts";
import { expectedOf } from "./expected.ts";
import { SimFunctions, VerifyFunctions } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const tests = import.meta.dirname;

const lean = new Lean();
after(() => lean.close());

/** The examples of a ChoiceDependent violation, which must search some processing. */
const relationExamples = new Set(runGroupExamples("choiceDependent").filter((root) => expectedOf(root).length > 0));

const simRoots = [join(tests, "../samples/todo/spec"), ...runExamples()];

// Every spec loads before any test runs, so that no test ends while a later one is still being registered.
const simCases = await Promise.all(
  simRoots.map(async (root) => {
    const spec = await loadSpec(root);
    const scenarios = spec.scenarios.map(({ service, name, definition }) => {
      const searched: Searched[] = [];
      stepOrderChanges(spec, definition.scenario, simulateSpec(spec, definition.scenario), 0, (s) => searched.push(s));
      const assigned = assignmentSearch(spec, definition.scenario);
      return { label: `${service}/${name}`, scenario: definition.scenario, searched, assigned };
    });
    return { root, spec, scenarios };
  }),
);

const assignedOf = (scenarios: readonly { readonly assigned: AssignmentSearch }[]) =>
  scenarios.filter((s) => s.assigned.tried.length > 0 || s.assigned.found.length > 0);

for (const { root, spec, scenarios } of simCases) {
  const searches = scenarios.flatMap((s) => s.searched);
  if (searches.length === 0 && (!relationExamples.has(root) || assignedOf(scenarios).length > 0)) continue;
  test(`${relative(tests, root)}: TS and Lean run the same step-order searches, with the same orders, verdicts, and violations`, (t) => {
    assert.ok(searches.length > 0, "each example of a ChoiceDependent violation searches some processing");
    for (const { label, scenario, searched } of scenarios) {
      const functions = new SimFunctions(spec, (part) => lean.read(part));
      const verify = new VerifyFunctions(spec);
      const fromLean = lean.stepOrderChanges(spec, scenario, {
        answer: (message) => (message["type"] === "comparableValue" ? verify : functions).answer(message),
      });
      assert.deepEqual(fromLean, JSON.parse(JSON.stringify(searched)), label);
    }
    const tried = searches.flatMap((s) => s.tried);
    t.diagnostic(
      `${searches.length} searches, ${tried.length} orders (${tried.filter((o) => "refused" in o).length} refused), ${searches.flatMap((s) => s.found).length} findings`,
    );
  });
}

test("stepOrderLimit is Lean's", () => {
  assert.equal(stepOrderLimit, lean.names().stepOrderLimit);
});

for (const { root, spec, scenarios } of simCases) {
  if (assignedOf(scenarios).length === 0) continue;
  test(`${relative(tests, root)}: TS and Lean run the same assignment searches of the handles of requests, with the same assignments and violations`, () => {
    for (const { label, scenario, assigned } of scenarios) {
      const functions = new SimFunctions(spec, (part) => lean.read(part));
      const verify = new VerifyFunctions(spec);
      const fromLean = lean.assignmentChanges(spec, scenario, {
        answer: (message) => (message["type"] === "comparableValue" ? verify : functions).answer(message),
      });
      assert.deepEqual(fromLean, JSON.parse(JSON.stringify(assigned)), label);
    }
  });
}

test("assignmentLimit is Lean's", () => {
  assert.equal(assignmentLimit, lean.names().assignmentLimit);
});
