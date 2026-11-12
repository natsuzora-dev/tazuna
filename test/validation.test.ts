import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import { basename, join } from "node:path";
import { test } from "node:test";
import { illegalKinds } from "../src/data/illegal.generated.ts";
import { folders, groupExamples } from "./examples.ts";
import { testEveryKind, testExamples } from "./expected.ts";

const illegalRoot = join(import.meta.dirname, "validation/illegal");

test("The folder names directly under test/validation/illegal are the file names of src/validation except check.ts", () => {
  const targets = readdirSync(join(import.meta.dirname, "../src/validation"))
    .filter((file) => file !== "check.ts")
    .map((file) => basename(file, ".ts"));
  assert.deepEqual(new Set(folders(illegalRoot).map((folder) => basename(folder))), new Set(targets));
});

testExamples(groupExamples("validation", "illegal"), "Illegal", ["check", "."]);

testEveryKind(groupExamples("validation"), illegalKinds);
