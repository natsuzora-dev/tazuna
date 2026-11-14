import assert from "node:assert/strict";
import { test } from "node:test";
import type { Note } from "../src/semantics/note.ts";
import { recordSource } from "../src/semantics/service/records.ts";

test("recordSource gives the keys in code-point order, so that spec functions are called in one order", () => {
  const row = { value: {}, encoded: {} };
  const keyed = new Map([
    [
      "Task",
      new Map([
        ["\u{1F600}", row],
        ["\u{FF61}", row],
      ]),
    ],
  ]);
  const note = { readRecord: () => {} } as unknown as Note;
  assert.deepEqual(recordSource({ keyed, singles: new Map() }, note).keys("Task"), ["\u{FF61}", "\u{1F600}"]);
});
