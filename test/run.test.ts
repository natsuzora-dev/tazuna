import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import { basename, join, relative } from "node:path";
import { test } from "node:test";
import {
  folders,
  isServiceFolder,
  leanDefinitionPaths,
  leanModulePaths,
  runExamples,
  runGroupExamples,
  runRoot,
  serviceRoot,
  subjects,
} from "./examples.ts";
import { exampleTest, expected, expectedOf, kindOfLine } from "./expected.ts";

const tests = import.meta.dirname;

/**
 * The kinds of each group. Its examples are in test/run/<group with a lowercase first letter>/<path>/<example>, where
 * <path> is the path, relative to lean/Tazuna, of the one Lean file that reports the violations of the example's
 * scenarios: the Sim file that reports the InvalidScenario violations, the Service file that calls State.report, Processing.report or State.reportAll, or the Explore file
 * that builds the BagOrderDependent, ChoiceDependent, or Undecided violations. An example without violations is in the
 * same folder as the example that it counters.
 */
const groups = [
  "InvalidScenario",
  "InvalidInput",
  "Fault",
  "BagOrderDependent",
  "ChoiceDependent",
  "Undecided",
] as const;

/** The kinds of another group that an example reports besides those of its own, each example with the reason. */
const otherGroupKinds: Readonly<Record<string, { readonly kinds: readonly string[]; readonly because: string }>> = {
  "choiceDependent/Explore/ChoiceDependent/halted-later": {
    kinds: ["Fault.outputSchema"],
    because: "the fault halts the scenario at its last line, and the stepOrder of its first line is still reported",
  },
};

const folderOf = (group: string) => group.charAt(0).toLowerCase() + group.slice(1);

const groupFolderExamples = groups.flatMap((group) => runGroupExamples(folderOf(group)));

test("The folder names directly under test/run are the group names of groups with a lowercase first letter", () => {
  assert.deepEqual(new Set(folders(runRoot).map((folder) => basename(folder))), new Set(groups.map(folderOf)));
});

test("Every folder under test/service and test/run/<group> is a Lean module path, an ancestor of one, or an example directly under one or inside it, and every file is inside an example. The modules are those of lean/Tazuna/Service for test/service and of lean/Tazuna outside Thm for test/run/<group>", () => {
  const roots = [
    { root: serviceRoot, modules: leanModulePaths("Service") },
    ...folders(runRoot).map((root) => ({ root, modules: leanDefinitionPaths() })),
  ];
  for (const { root, modules } of roots) {
    const inExample = (path: string) => modules.some((module) => path.startsWith(`${module}/`));
    const onModulePath = (path: string) => modules.some((module) => `${module}/`.startsWith(`${path}/`));
    const misplaced = readdirSync(root, { recursive: true, withFileTypes: true })
      .filter((entry) => {
        const parent = relative(root, entry.parentPath);
        const path = join(parent, entry.name);
        return entry.isDirectory() ? !onModulePath(path) && !inExample(path) : !inExample(parent);
      })
      .map((entry) => relative(root, join(entry.parentPath, entry.name)));
    assert.deepEqual(misplaced, [], relative(tests, root));
  }
});

test("Each test/service subject and test/run example holds only service folders and expected.jsonl", () => {
  for (const example of [...subjects(), ...groupFolderExamples])
    for (const entry of readdirSync(example, { withFileTypes: true }))
      assert.ok(
        entry.isDirectory() ? isServiceFolder(join(example, entry.name)) : entry.name === expected,
        relative(tests, join(example, entry.name)),
      );
});

for (const example of runExamples()) test(relative(tests, example), (t) => exampleTest(t, example));

test("The expected.jsonl of each test/service and test/sim subject is empty", () => {
  for (const subject of subjects()) assert.deepEqual(expectedOf(subject), [], relative(tests, subject));
});

for (const group of groups) {
  const examples = runGroupExamples(folderOf(group));
  test(`The kinds in the expected.jsonl of the examples under test/run/${folderOf(group)} are kinds of ${group}`, () => {
    for (const example of examples)
      assert.deepEqual(
        expectedOf(example)
          .map(kindOfLine)
          .filter(
            (kind) =>
              !kind.startsWith(`${group}.`) &&
              !(otherGroupKinds[relative(runRoot, example)]?.kinds.includes(kind) ?? false),
          ),
        [],
        relative(tests, example),
      );
  });
}
