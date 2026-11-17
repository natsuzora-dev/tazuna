import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import { basename, join, relative } from "node:path";
import { test } from "node:test";
import { bagOrderDependentKinds } from "../src/data/bagOrderDependent.generated.ts";
import { choiceDependentKinds } from "../src/data/choiceDependent.generated.ts";
import { faultKinds } from "../src/data/fault.generated.ts";
import { invalidInputKinds } from "../src/data/invalidInput.generated.ts";
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
import { exampleTest, expected, expectedOf, kindOfLine, testEveryKind } from "./expected.ts";

const tests = import.meta.dirname;

/**
 * The kinds of each group. Its examples are in test/run/<group with a lowercase first letter>/<path>/<example>, where
 * <path> is the path, relative to lean/Tazuna, of the one Lean file that reports the violations of the example's
 * scenarios: the Service file that calls State.report, Processing.report or State.reportAll, or the Explore file
 * that builds the BagOrderDependent or ChoiceDependent violations. An example without violations is in the
 * same folder as the example that it counters.
 */
const groups: Readonly<Record<string, readonly string[]>> = {
  InvalidInput: invalidInputKinds,
  Fault: faultKinds,
  BagOrderDependent: bagOrderDependentKinds,
  ChoiceDependent: choiceDependentKinds,
};

const unexemplified: Readonly<Record<string, Readonly<Record<string, string>>>> = {
  InvalidInput: {
    "InvalidInput.unownedTarget":
      "Only a data scenario names a target that its receiver does not own (the DSL's types let the client send only the definitions of the service it names); test/sim/Run/network/unownedTarget exemplifies it",
    "InvalidInput.unlistedRejectionReason":
      "The type of an answer accepts as the reason of a requires rejection only a requires condition of the request",
    "InvalidInput.unknownControl":
      "The type of operate accepts only the controls of the screen, and the exploration of test operates only those",
    "InvalidInput.unreadyStep":
      "Only test's step-order search writes a step order, naming only the steps that an execution took",
    "InvalidInput.unusedStepOrder":
      "Only test's step-order search writes a step order, naming only the steps that an execution took",
  },
  ChoiceDependent: {
    "ChoiceDependent.uncomparable":
      "verify binds each created key at its first place in the outputs, so the records compare under bindings that fix every created key, unless the outputs cannot be compared with themselves; an example needs equal requests with different answers and seven created records that only their keys tell apart",
  },
  Fault: {
    "Fault.exceededMessageWork":
      "An example that reaches the limit 100000 writes about 8300 event lines in one message and makes run.diff several times slower",
    "Fault.exceededExitDepth": "Reaching the exit nesting limit 100 takes about 50 nested screen definitions",
  },
};

/** The kinds of another group that an example reports besides those of its own, each example with the reason. */
const otherGroupKinds: Readonly<Record<string, { readonly kinds: readonly string[]; readonly because: string }>> = {
  "choiceDependent/Explore/ChoiceDependent/halted-later": {
    kinds: ["Fault.outputSchema"],
    because: "the fault halts the scenario at its last line, and the stepOrder of its first line is still reported",
  },
  "choiceDependent/Explore/ChoiceDependent/identical-requests": {
    kinds: ["InvalidScenario.leftInFlight", "InvalidScenario.unresolvedReference"],
    because:
      "each handle of requests needs a line of its own, and a handle beyond the requests sent names nothing, beside the assignments that the example searches",
  },
};

const folderOf = (group: string) => group.charAt(0).toLowerCase() + group.slice(1);

const groupFolderExamples = Object.keys(groups).flatMap((group) => runGroupExamples(folderOf(group)));

test("The folder names directly under test/run are the group names of groups with a lowercase first letter", () => {
  assert.deepEqual(
    new Set(folders(runRoot).map((folder) => basename(folder))),
    new Set(Object.keys(groups).map(folderOf)),
  );
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

for (const [group, kinds] of Object.entries(groups)) {
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
  testEveryKind(examples, kinds, unexemplified[group]);
}
