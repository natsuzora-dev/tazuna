import assert from "node:assert/strict";
import { join, relative } from "node:path";
import { test } from "node:test";
import { exampleFolders, explanations } from "../../scripts/explain.ts";
import { explain } from "../../src/cli/explain.ts";
import { isUserKind, kinds } from "../../src/data/kinds.ts";
import { builtExplanations, expectedOf, kindOfLine } from "../fixtures/fixtures.ts";

const maxExcerptLines = 40;
const built = explanations();
const kindEntries = kinds.filter(isUserKind).map((kind) => [kind, built.kinds[kind]] as const);

test("Each group and each kind has a doc comment", () => {
  assert.deepEqual(
    Object.entries(built.groups).filter(([, doc]) => doc === ""),
    [],
  );
  assert.deepEqual(
    kindEntries.filter(([, k]) => k.meaning === ""),
    [],
  );
});

test("Each kind that a user meets has one example, the fixture named after it, which reports that kind and no other, and no internal kind has one", () => {
  const folders = exampleFolders();
  assert.deepEqual(
    kinds.filter((kind) => folders.filter(([k]) => k === kind).length !== (isUserKind(kind) ? 1 : 0)),
    [],
  );
  assert.deepEqual(
    folders
      .filter(([kind, dir]) => {
        const reported = expectedOf(dir).map(kindOfLine);
        return reported.length === 0 || reported.some((k) => k !== kind);
      })
      .map(([, dir]) => relative(join(import.meta.dirname, "../.."), dir)),
    [],
  );
});

test(`Each example's excerpt has at most ${maxExcerptLines} lines and holds the reported line`, () => {
  assert.deepEqual(
    kindEntries
      .flatMap(([kind, k]) => (k.example?.excerpt === undefined ? [] : [{ kind, ...k.example.excerpt }]))
      .filter(({ from, to, line }) => to - from >= maxExcerptLines || line < from || line > to)
      .map(({ kind }) => kind),
    [],
  );
});

test("explain gives the kind's meaning, group, reporters, side at fault, and example, and names an unknown kind, an internal kind, and a missing explain.json as misuses", () => {
  const explained = explain("Fault.failedEnsures", builtExplanations());
  assert.ok("explanation" in explained);
  const { example, ...rest } = explained.explanation;
  assert.deepEqual(rest, {
    kind: "Fault.failedEnsures",
    meaning: built.kinds["Fault.failedEnsures"].meaning,
    group: "Fault",
    groupMeaning: built.groups.Fault,
    reportedBy: ["test", "verify", "prove"],
    fixedIn: "The spec.",
    halts: false,
  });
  assert.deepEqual(example, built.kinds["Fault.failedEnsures"].example);
  assert.deepEqual(explain("Fault.data"), { misuse: "unknown kind Fault.data" });
  assert.deepEqual(explain("constructor"), { misuse: "unknown kind constructor" });
  assert.deepEqual(explain("InvalidInput.unownedTarget"), {
    misuse:
      "InvalidInput.unownedTarget is internal to tazuna, and a spec that check passes never reports it. Report it as a bug",
  });
  assert.deepEqual(explain("Fault.failedEnsures", "/missing/explain.json"), {
    misuse: "/missing/explain.json is missing. Reinstall tazuna",
  });
});
