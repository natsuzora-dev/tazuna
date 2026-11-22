import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { typeCheck } from "../src/check/typeCheck.ts";

const root = join(import.meta.dirname, "..");

/** The tsc output for `source`, a file next to the spec of the ToDo sample's todo service. */
function errorsOf(source: string): string {
  mkdirSync(join(import.meta.dirname, ".fixtures"), { recursive: true });
  const project = mkdtempSync(join(import.meta.dirname, ".fixtures", "type-errors-"));
  try {
    writeFileSync(
      join(project, "tsconfig.json"),
      JSON.stringify({ extends: "../../../tsconfig.json", include: ["probe.ts"] }),
    );
    writeFileSync(join(project, "probe.ts"), source);
    const checked = typeCheck(project, root);
    assert.equal(checked.kind, "typeErrors");
    return checked.kind === "typeErrors" ? checked.output : "";
  } finally {
    rmSync(project, { recursive: true, force: true });
  }
}

test("A wrong answer in answered reports the part of the answer that differs, not the kind of line", () => {
  const output = errorsOf(`
import { answered, rejected } from "@natsuzora-dev/tazuna";
import { completeTask } from "../../../samples/todo/spec/todo/commands.ts";
import { scenario } from "../../../samples/todo/spec/todo/data.ts";

export const typo = scenario({
  description: "typo",
  given: { start: 1_792_890_000_000, records: { Task: [], Settings: { shouldRemind: true } }, peers: [] },
  when: (w) => ({ first: w.client.send(completeTask, { taskId: "task-1" }) }),
  then: ({ first }) => [answered(first, rejected("requires", "notCompletedTypo"))],
});
`);
  assert.match(output, /Type '"notCompletedTypo"' is not assignable to type '"notCompleted"/);
  assert.doesNotMatch(output, /subscribes/);
});
