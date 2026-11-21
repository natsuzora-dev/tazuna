import assert from "node:assert/strict";
import { basename, join, relative } from "node:path";
import { test } from "node:test";
import { folders } from "./examples.ts";
import { kindOfLine, recordsOf, testExamples } from "./expected.ts";

const groups = { mismatch: "Mismatch", uncomparable: "Uncomparable" } as const;

const verify = ["verify", ".", "traces"];

/** The command that runs the examples of each target, test/verify/<group>/<target>. */
const commands: Readonly<Record<string, readonly string[]>> = {
  compare: verify,
  external: verify,
  lines: verify,
  pairing: verify,
  snapshot: ["test", "."],
};

const verifyRoot = join(import.meta.dirname, "verify");

test("The folder names directly under test/verify/<group> are the targets of commands", () => {
  const targets = Object.keys(groups).flatMap((group) => folders(join(verifyRoot, group)).map((t) => basename(t)));
  assert.deepEqual(new Set(targets), new Set(Object.keys(commands)));
});

for (const [folder, group] of Object.entries(groups))
  for (const [target, args] of Object.entries(commands))
    testExamples(folders(join(verifyRoot, folder, target)), group, args);

const snapshotChecks = Object.values(groups).map((group) => `${group}.`);

test("tazuna test, exploration included, finds no violation in the spec of each verify example besides its snapshot comparisons", async () => {
  const verified = Object.keys(groups).flatMap((folder) =>
    Object.entries(commands)
      .filter(([, args]) => args === verify)
      .flatMap(([target]) => folders(join(verifyRoot, folder, target))),
  );
  for (const example of verified) {
    const kinds = (await recordsOf(example, [commands["snapshot"] ?? []])).map(kindOfLine);
    assert.deepEqual(
      kinds.filter((kind) => !snapshotChecks.some((group) => kind.startsWith(group))),
      [],
      relative(import.meta.dirname, example),
    );
  }
});
