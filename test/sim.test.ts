import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { test } from "node:test";
import { ask } from "../src/cli/engine.ts";
import { invalidScenarioKinds } from "../src/data/invalidScenario.generated.ts";
import { scenario } from "../src/data/scenario.generated.ts";
import { convertedSpec, leanModulePaths, outcomeSuffix, scenarioSuffix, simExamples, simRoot } from "./examples.ts";
import { folders, isServiceFolder } from "./fixtures/fixtures.ts";

const tests = import.meta.dirname;
const examples = simExamples();

test("Every folder under test/sim is a Lean Sim module path or an example directly under one, and each example holds only service folders and pairs of <name>.scenario.json and <name>.expected.json", () => {
  const modules = leanModulePaths("Sim");
  const examplePaths = new Set(examples.map(({ root }) => relative(simRoot, root)));
  const onModulePath = (path: string) => modules.some((module) => `${module}/`.startsWith(`${path}/`));
  const misplaced = readdirSync(simRoot, { recursive: true, withFileTypes: true }).filter((entry) => {
    const parent = relative(simRoot, entry.parentPath);
    const path = join(parent, entry.name);
    const inExample = [...examplePaths].some((e) => path.startsWith(`${e}/`));
    if (inExample) return false;
    if (examplePaths.has(path)) return false;
    return !(entry.isDirectory() && onModulePath(path));
  });
  assert.deepEqual(
    misplaced.map((e) => relative(simRoot, join(e.parentPath, e.name))),
    [],
  );
  for (const { root, scenarios } of examples)
    for (const entry of readdirSync(root, { withFileTypes: true })) {
      const name = entry.name;
      const pairs = scenarios.some((s) => name === `${s}${scenarioSuffix}` || name === `${s}${outcomeSuffix}`);
      assert.ok(entry.isDirectory() ? isServiceFolder(join(root, name)) : pairs, relative(tests, join(root, name)));
    }
  assert.ok(folders(simRoot).length > 0);
});

const outcomes = new Map<string, readonly string[]>();

for (const { root, scenarios } of examples) {
  const spec = await convertedSpec(root);
  for (const name of scenarios)
    test(`${relative(tests, root)}/${name}: the simulation gives the outcome of ${name}${outcomeSuffix}`, (t) => {
      const sc = scenario.parse(JSON.parse(readFileSync(join(root, `${name}${scenarioSuffix}`), "utf8")));
      const [outcome] = ask("simulate", [{ structure: spec.structure, scenario: sc }]);
      if (outcome === undefined) throw new Error("the engine gave no outcome");
      outcomes.set(`${root}/${name}`, [
        ...outcome.violations.map((r) => r.kind),
        ...(outcome.halted === null ? [] : [outcome.halted.kind]),
      ]);
      t.assert.fileSnapshot(outcome, join(root, `${name}${outcomeSuffix}`), {
        serializers: [(v) => `${JSON.stringify(v, null, 2)}\n`],
      });
    });
}

test("Each InvalidScenario kind is in the expected outcome of some scenario under test/sim", () => {
  const reported = new Set(
    examples.flatMap(({ root, scenarios }) =>
      scenarios.flatMap((name) => {
        const outcome = JSON.parse(readFileSync(join(root, `${name}${outcomeSuffix}`), "utf8")) as {
          readonly violations: readonly { readonly kind: string }[];
          readonly halted: { readonly kind: string } | null;
        };
        return [...outcome.violations.map((r) => r.kind), ...(outcome.halted === null ? [] : [outcome.halted.kind])];
      }),
    ),
  );
  assert.deepEqual(
    invalidScenarioKinds.filter((kind) => !reported.has(kind)),
    [],
  );
});
