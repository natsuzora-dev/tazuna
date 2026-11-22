import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import { basename, join } from "node:path";
import { test } from "node:test";
import { folders, groupExamples } from "./examples.ts";
import { testExamples } from "./expected.ts";

const roots = { illegal: "Illegal", nonCanonical: "NonCanonical" } as const;

test("The folder names directly under test/validation/<group> are the module names of lean/Tazuna/Validation with a lowercase first letter, except Check, Illegal and NonCanonical", () => {
  const targets = readdirSync(join(import.meta.dirname, "../lean/Tazuna/Validation"))
    .map((file) => basename(file, ".lean"))
    .filter((name) => !["Check", "Illegal", "NonCanonical"].includes(name))
    .map((name) => name.charAt(0).toLowerCase() + name.slice(1));
  const named = Object.keys(roots).flatMap((group) =>
    folders(join(import.meta.dirname, "validation", group)).map((folder) => basename(folder)),
  );
  assert.deepEqual(named.toSorted(), targets.toSorted());
});

for (const [folder, group] of Object.entries(roots))
  testExamples(groupExamples("validation", folder), group, ["check", "."]);
