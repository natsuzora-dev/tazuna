import assert from "node:assert/strict";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { testSpec } from "../src/cli/test.ts";
import type { Candidate } from "../src/explore/orders.ts";
import { type DecidedOrder, stepOrderChanges } from "../src/explore/stepOrders.ts";
import type { Spec } from "../src/load/load.ts";
import { loadSpec } from "../src/load/load.ts";
import { stepOrderLimit } from "../src/observe/choiceDependent.ts";
import { type Run, stepsOf } from "../src/sim/spec/execute.ts";
import { simulateSpec } from "../src/sim/spec/simulate.ts";
import { depth, loadRoot, runExamples, runGroupExamples } from "./examples.ts";
import { type Answering, RunFunctions, SimFunctions, VerifyFunctions } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const tests = import.meta.dirname;

const lean = new Lean();
after(() => lean.close());

/**
 * Returns the answers to Lean's questions about the spec functions of its runs and the comparable values that verify
 * reads.
 */
function answering(spec: Spec, service: string): Answering {
  const run = new RunFunctions(spec, service, (part) => lean.read(part));
  const verify = new VerifyFunctions(spec);
  return { answer: (message) => (message["type"] === "comparableValue" ? verify : run).answer(message) };
}

const roots = await Promise.all(runExamples().map(async (root) => ({ root, spec: await loadRoot(root) })));
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

for (const { root, spec } of roots) {
  const candidates: Candidate[] = [];
  if (spec.legacyScenarios.length === 0) continue;
  testSpec(spec, { update: false, depth, decided: (candidate) => candidates.push(candidate) });
  if (candidates.length === 0 && !relationExamples.has(root)) continue;
  test(`${relative(tests, root)}: TS and Lean find the same ChoiceDependent violations for each pair of choices that explore compares`, (t) => {
    assert.ok(
      candidates.length > 0,
      "explore compares pairs of choices in each example of a ChoiceDependent violation",
    );
    let found = 0;
    for (const { kind, runs, found: ts } of candidates) {
      const [first, second] = runs;
      const service = first.execution.processing.st.service;
      const steps = (run: Run) => stepsOf(spec, service, run.execution.inputs);
      const fromLean = lean.choice(spec, service, kind, steps(first), steps(second), answering(spec, service));
      const expected =
        ts === undefined
          ? null
          : JSON.parse(JSON.stringify({ kind: ts.kind, definition: ts.definition, data: ts.data }));
      assert.deepEqual(fromLean, expected, `${kind} after steps ${JSON.stringify(steps(first))}`);
      if (ts !== undefined) found += 1;
    }
    t.diagnostic(`${candidates.length} candidates, ${found} findings`);
  });
}

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
