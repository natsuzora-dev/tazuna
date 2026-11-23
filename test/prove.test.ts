import assert from "node:assert/strict";
import { basename, join, relative } from "node:path";
import { test } from "node:test";
import { folders } from "./examples.ts";
import { expected, proveLinesOf } from "./expected.ts";

const proveRoot = join(import.meta.dirname, "prove");

const verdicts = ["proved", "counterexample", "undecided"] as const;

/** The exit code of prove when every property has the verdict. */
const exitCodes = { proved: 0, counterexample: 1, undecided: 2 } as const;

const jsonl = (lines: readonly string[]) => lines.map((line) => `${line}\n`).join("");

test("The folder names directly under test/prove are the verdicts of prove", () => {
  assert.deepEqual(new Set(folders(proveRoot).map((folder) => basename(folder))), new Set(verdicts));
});

for (const verdict of verdicts)
  for (const example of folders(join(proveRoot, verdict)))
    test(relative(import.meta.dirname, example), async (t) => {
      const { lines, code } = await proveLinesOf(example);
      assert.equal(code, exitCodes[verdict]);
      t.assert.fileSnapshot(lines, join(example, expected), { serializers: [jsonl] });
      assert.deepEqual(
        lines.map((line) => (JSON.parse(line) as { readonly verdict: { readonly kind: string } }).verdict.kind),
        lines.map(() => verdict),
      );
    });
