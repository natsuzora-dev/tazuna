import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { after, type TestContext, test } from "node:test";
import { main } from "../src/cli/main.ts";
import { Converter } from "../src/convert/program.ts";
import { groups } from "../src/data/groups.ts";
import { parseKind } from "../src/data/kinds.ts";
import type { Group, ReportedViolation } from "../src/data/violation.ts";
import { maskedStack, typeChecked } from "./examples.ts";

export const expected = "expected.jsonl";

let shared: Converter | undefined;
after(() => shared?.close());

/** The converter that the examples of this test file share, since each converter starts tsgo. */
const converter = (): Converter => {
  shared ??= new Converter();
  return shared;
};

const summaryOnly = /^[^:\n]+: (?:no violations|\d+ violations?)$/;

/**
 * The violation lines of the runs of `example`, each checked to be of a group whose reportedBy lists the command that
 * reported it.
 */
export async function recordsOf(example: string, runs: readonly (readonly string[])[]): Promise<readonly string[]> {
  const logged: string[] = [];
  for (const args of runs) {
    const [name = ""] = args;
    const commands = [name, ...(args.includes("--coverage") ? [`${name} --coverage`] : [])];
    await main(args, {
      cwd: example,
      log: (line) => {
        const violation = JSON.parse(line) as ReportedViolation;
        const group = parseKind(violation.kind)?.group;
        assert.ok(
          group !== undefined && groups[group].reportedBy.some((c) => commands.includes(c)),
          `${violation.kind} from tazuna ${args.join(" ")}`,
        );
        logged.push(JSON.stringify(maskedStack(violation)));
      },
      error: (line) => assert.match(line, summaryOnly, `tazuna ${args.join(" ")}`),
      // An example with a tsconfig.json of its own runs tsc, for the violations that only tsc's program shows.
      ...(existsSync(join(example, "tsconfig.json")) ? {} : { typeCheck: () => typeChecked, converter: converter() }),
    });
  }
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
  compareWithExpected(t, example, [["test", "."]]);

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
