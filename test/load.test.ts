import assert from "node:assert/strict";
import { join } from "node:path";
import { test } from "node:test";
import { loadSpec } from "../src/load/load.ts";
import { groupExamples } from "./examples.ts";
import { testExamples } from "./expected.ts";

const groups = { malformed: "Malformed", nonCanonical: "NonCanonical", restricted: "Restricted" } as const;

for (const [folder, group] of Object.entries(groups))
  testExamples(groupExamples("load", folder), group, ["check", "."]);

test("Loading stops with an internal error on an automation whose commands hold two entries, which only `any` lets past OneKey", async () => {
  await assert.rejects(loadSpec(join(import.meta.dirname, "bug/automationEntries")), {
    message: "an automation's commands holds 2 entries, where its type allows one",
  });
});
