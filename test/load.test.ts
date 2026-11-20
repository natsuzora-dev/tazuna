import assert from "node:assert/strict";
import { join } from "node:path";
import { test } from "node:test";
import { checkSpecWith } from "../src/check/spec.ts";
import { groupExamples, typeChecked } from "./examples.ts";
import { testExamples } from "./expected.ts";

const groups = { malformed: "Malformed", nonCanonical: "NonCanonical", restricted: "Restricted" } as const;

for (const [folder, group] of Object.entries(groups))
  testExamples(groupExamples("load", folder), group, ["check", "."]);

test("check calls a spec unloadable when a definition names no definition and no violation says why", async () => {
  assert.deepEqual(await checkSpecWith(join(import.meta.dirname, "load/unloadable"), typeChecked), {
    kind: "unloadable",
    reason: "the automation worklist.copyTask commands names no definition",
  });
});
