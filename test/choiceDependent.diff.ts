import assert from "node:assert/strict";
import { join, relative } from "node:path";
import { after, test } from "node:test";
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
    const spec = (await loadSpec(root)).spec;
    const scenarios = spec.scenarios.map(({ service, name, definition }) => {
      const searched: Searched[] = [];
      stepOrderChanges(spec, definition.scenario, simulateSpec(spec, definition.scenario), 0, (s) => searched.push(s));
      return { label: `${service}/${name}`, scenario: definition.scenario, searched };
    });
    return { root, spec, scenarios };
  }),
);

for (const { root, spec, scenarios } of simCases) {
  const searches = scenarios.flatMap((s) => s.searched);
  if (searches.length === 0 && !relationExamples.has(root)) continue;
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
