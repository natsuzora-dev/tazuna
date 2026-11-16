import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { scenario } from "../src/data/scenario.generated.ts";
import { canonicalJson, type Json } from "../src/data/values.ts";
import { loadSpec } from "../src/load/load.ts";
import { outcomeOf, simulateSpec } from "../src/sim/spec/simulate.ts";
import { outcomeSuffix, runExamples, scenarioSuffix, simExamples } from "./examples.ts";
import { SimFunctions } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

const roots = [join(import.meta.dirname, "../samples/todo/spec"), ...runExamples()];

// Every spec loads before any test runs, so that no test ends while a later one is still being registered.
const examples = await Promise.all(
  simExamples().map(async ({ root, scenarios }) => ({ root, scenarios, spec: await loadSpec(root) })),
);
const rootSpecs = await Promise.all(roots.map(async (root) => ({ root, spec: await loadSpec(root) })));

for (const { root, scenarios, spec } of examples) {
  for (const name of scenarios)
    test(`${relative(join(import.meta.dirname, ".."), root)}/${name}: Lean and TS simulate the scenario alike, and the outcome is ${name}${outcomeSuffix}`, () => {
      const sc = scenario.parse(JSON.parse(readFileSync(join(root, `${name}${scenarioSuffix}`), "utf8")));
      const ts = outcomeOf(simulateSpec(spec, sc));
      const fromLean = lean.simulate(spec, sc, new SimFunctions(spec, (part) => lean.read(part)));
      assert.equal(canonicalJson(fromLean as Json), canonicalJson(ts as unknown as Json));
      assert.equal(
        canonicalJson(ts as unknown as Json),
        canonicalJson(JSON.parse(readFileSync(join(root, `${name}${outcomeSuffix}`), "utf8")) as Json),
      );
    });
}

for (const { root, spec } of rootSpecs) {
  for (const { service, name, definition } of spec.scenarios)
    test(`${relative(join(import.meta.dirname, ".."), root)}: Lean and TS simulate ${service}/${name} alike`, () => {
      const ts = outcomeOf(simulateSpec(spec, definition.scenario));
      const fromLean = lean.simulate(spec, definition.scenario, new SimFunctions(spec, (part) => lean.read(part)));
      assert.equal(canonicalJson(fromLean as Json), canonicalJson(ts as unknown as Json));
    });
}
