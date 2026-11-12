import assert from "node:assert/strict";
import { test } from "node:test";
import { type RecordSource, reversedKeys } from "../src/semantics/service/records.ts";

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
