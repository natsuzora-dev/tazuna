import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { test } from "node:test";
import { ask } from "../../src/cli/engine.ts";
import { invalidScenarioKinds } from "../../src/data/invalidScenario.generated.ts";
import { scenario } from "../../src/data/scenario.generated.ts";
import { isServiceFolder } from "../fixtures/fixtures.ts";
import { convertedSpec, outcomeSuffix, scenarioSuffix, simExamples } from "./simulate.ts";

const tests = import.meta.dirname;
const examples = simExamples();

test("Each example holds only service folders and pairs of <name>.scenario.json and <name>.expected.json", () => {
  for (const { root, scenarios } of examples)
    for (const entry of readdirSync(root, { withFileTypes: true })) {
      const name = entry.name;
      const pairs = scenarios.some((s) => name === `${s}${scenarioSuffix}` || name === `${s}${outcomeSuffix}`);
      assert.ok(entry.isDirectory() ? isServiceFolder(join(root, name)) : pairs, relative(tests, join(root, name)));
    }
  assert.ok(examples.length > 0);
});

for (const { root, scenarios } of examples) {
  const spec = await convertedSpec(root);
  for (const name of scenarios)
    test(`${relative(tests, root)}/${name}: the simulation gives the outcome of ${name}${outcomeSuffix}`, (t) => {
      const sc = scenario.parse(JSON.parse(readFileSync(join(root, `${name}${scenarioSuffix}`), "utf8")));
      const [outcome] = ask("test", { structure: spec.structure, scenarios: [sc] }).runs;
      if (outcome === undefined) throw new Error("the engine gave no outcome");
      t.assert.fileSnapshot(outcome, join(root, `${name}${outcomeSuffix}`), {
        serializers: [(v) => `${JSON.stringify(v, null, 2)}\n`],
      });
    });
}

test("Each InvalidScenario kind is in the expected outcome of some scenario under test/unit/simulate", () => {
  const reported = new Set(
    examples.flatMap(({ root, scenarios }) =>
      scenarios.flatMap((name) => {
        const outcome = JSON.parse(readFileSync(join(root, `${name}${outcomeSuffix}`), "utf8")) as {
          readonly violations: readonly { readonly kind: string }[];
        };
        return outcome.violations.map((r) => r.kind);
      }),
    ),
  );
  assert.deepEqual(
    invalidScenarioKinds.filter((kind) => !reported.has(kind)),
    [],
  );
});
