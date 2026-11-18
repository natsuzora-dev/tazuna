import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { scenario } from "../src/data/scenario.generated.ts";
import { canonicalJson, type Json } from "../src/data/values.ts";
import { loadSpec } from "../src/load/load.ts";
import { outcomeOf, simulateSpec } from "../src/sim/spec/simulate.ts";
import { outcomeSuffix, runExamples, runGroupExamples, scenarioSuffix, serviceRoot, simExamples } from "./examples.ts";
import { SimFunctions } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

const roots = [join(import.meta.dirname, "../samples/todo/spec"), ...runExamples()];

// Every spec loads before any test runs, so that no test ends while a later one is still being registered.
const examples = await Promise.all(
  simExamples().map(async ({ root, scenarios }) => ({ root, scenarios, spec: (await loadSpec(root)).spec })),
);
const rootSpecs = await Promise.all(roots.map(async (root) => ({ root, spec: (await loadSpec(root)).spec })));

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

const refusedRoots = [...runGroupExamples("choiceDependent"), join(serviceRoot, "Chart/Deadline/deadlines")];

test("Lean and TS refuse a step order that names a step no processing takes, as unreadyStep where the processing takes a queue step and as unusedStepOrder where it takes none, clock lines included", async () => {
  const kinds = new Set<string>();
  for (const root of refusedRoots) {
    const spec = (await loadSpec(root)).spec;
    for (const { definition } of spec.scenarios) {
      const sc = definition.scenario;
      for (const [index, line] of sc.lines.entries()) {
        const event = { service: sc.service, name: "noSuchAutomation" };
        const order = [{ kind: "reaction", automation: event.name, event, payload: {}, delivered: [] } as const];
        const stepOrders = [{ origin: { type: "line", index } as const, service: sc.service, order }];
        const ts = outcomeOf(simulateSpec(spec, sc, stepOrders));
        const fromLean = lean.simulate(spec, sc, new SimFunctions(spec, (part) => lean.read(part)), false, stepOrders);
        assert.equal(canonicalJson(fromLean as Json), canonicalJson(ts as unknown as Json), `${root} line ${index}`);
        const own = ts.services.find((p) => p.service === sc.service);
        for (const v of own?.violations ?? [])
          if (v.kind.endsWith("StepOrder") || v.kind.endsWith("Step")) kinds.add(`${v.kind} ${line.type}`);
      }
    }
  }
  for (const kind of ["InvalidInput.unreadyStep request", "InvalidInput.unusedStepOrder at"])
    assert.ok(kinds.has(kind), `${kind} among ${[...kinds].join(", ")}`);
});
