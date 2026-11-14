import assert from "node:assert/strict";
import { test } from "node:test";
import type { Note } from "../src/semantics/note.ts";
import { type RecordSource, recordSource, reversedKeys } from "../src/semantics/service/records.ts";

class Tasks implements RecordSource {
  keys() {
    return ["task-1", "task-2"];
  }
  exists(_entity: string, key: string) {
    return key === "task-1";
  }
  field(_entity: string, key: string | undefined) {
    return key === "task-1" ? "Buy milk" : undefined;
  }
}

test("reversedKeys reverses the keys and reads exists and field from the source, also from a class instance", () => {
  const reversed = reversedKeys(new Tasks());
  assert.deepEqual(reversed.keys("Task"), ["task-2", "task-1"]);
  assert.equal(reversed.exists("Task", "task-1"), true);
  assert.equal(reversed.field("Task", "task-1", "title"), "Buy milk");
});

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
