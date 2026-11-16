import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { dirname, join, relative, sep } from "node:path";
import { type TestContext, test } from "node:test";
import { main } from "../src/cli/main.ts";
import type { Problem } from "../src/data/problem.ts";
import type { Group } from "../src/data/violation.ts";
import { depth, maskedStack } from "./examples.ts";

export const expected = "expected.jsonl";

const summaryOnly = /^(Checked|Tested|Verified) [^\n]*\. (No problems found|\d+ problems?)\.$/;

export async function recordsOf(example: string, runs: readonly (readonly string[])[]): Promise<readonly string[]> {
  const logged: string[] = [];
  for (const args of runs)
    await main(args, {
      cwd: example,
      log: (line) => logged.push(JSON.stringify(maskedStack(JSON.parse(line) as Problem))),
      error: (line) => assert.match(line, summaryOnly, `tazuna ${args.join(" ")}`),
      typeCheck: () => ({ kind: "ran", passed: true, output: "" }),
    });
  return logged;
}

export const expectedOf = (example: string): string[] =>
  readFileSync(join(example, expected), "utf8")
    .split("\n")
    .filter((line) => line !== "");

const jsonl = (records: readonly string[]) => records.map((line) => `${line}\n`).join("");

async function compareWithExpected(
  t: TestContext,
  example: string,
  runs: readonly (readonly string[])[],
): Promise<void> {
  t.assert.fileSnapshot(await recordsOf(example, runs), join(example, expected), { serializers: [jsonl] });
}

/** Compares the violations that test reports on an example with its expected.jsonl. */
export const exampleTest = (t: TestContext, example: string): Promise<void> =>
  compareWithExpected(t, example, [["test", ".", "--depth", String(depth)]]);

export const kindOfLine = (line: string) => (JSON.parse(line) as { readonly kind: string }).kind;

/** Tests that the violations of each example equal its expected.jsonl and all have kinds of `group`. */
export function testExamples(examples: readonly string[], group: Group, args: readonly string[]): void {
  for (const example of examples)
    test(relative(import.meta.dirname, example), async (t) => {
      await compareWithExpected(t, example, [args]);
      assert.deepEqual(
        expectedOf(example)
          .map(kindOfLine)
          .filter((kind) => !kind.startsWith(`${group}.`)),
        [],
      );
    });
}

/** Returns the deepest folder that holds every example. */
function commonFolder(examples: readonly string[]): string {
  const parts = examples.map((example) => relative(import.meta.dirname, dirname(example)).split(sep));
  const first = parts[0] ?? [];
  let n = 0;
  while (n < first.length && parts.every((p) => p[n] === first[n])) n += 1;
  return first.slice(0, n).join(sep);
}

/**
 * Tests that each of `kinds` appears in the expected.jsonl of some example, except `unexemplified`: the kinds that no
 * example reports, each with the reason.
 */
export function testEveryKind(
  examples: readonly string[],
  kinds: readonly string[],
  unexemplified: Readonly<Record<string, string>> = {},
): void {
  const groups = [...new Set(kinds.map((kind) => kind.split(".")[0]))].join(" and ");
  const skipped = Object.keys(unexemplified);
  test(`Each kind of ${groups} except the unexemplified ones appears in the expected.jsonl of some example under test/${commonFolder(examples)}, and no unexemplified kind does`, () => {
    const reported = new Set(examples.flatMap(expectedOf).map(kindOfLine));
    assert.deepEqual(
      kinds.filter((kind) => !(kind in unexemplified) && !reported.has(kind)),
      [],
    );
    assert.deepEqual(
      skipped.filter((kind) => !kinds.includes(kind) || reported.has(kind)),
      [],
    );
  });
}
