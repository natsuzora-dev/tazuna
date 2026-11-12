import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { leanModulePaths } from "./examples.ts";

const lowerFirst = (path: string) =>
  path
    .split("/")
    .map((part) => part.charAt(0).toLowerCase() + part.slice(1))
    .join("/");

test("The .ts paths under src/semantics are the .lean paths under lean/Tazuna/Semantics with a lowercase first letter in each part (chart/exit.ts for Chart/Exit.lean), except InvalidInput.lean, Fault.lean, and Step.lean, which generate TS types in src/data", () => {
  const files = readdirSync(join(import.meta.dirname, "../src/semantics"), { recursive: true, encoding: "utf8" })
    .filter((file) => file.endsWith(".ts"))
    .map((file) => file.slice(0, -".ts".length));
  assert.deepEqual(
    new Set(files),
    new Set(
      leanModulePaths("Semantics")
        .filter((path) => path !== "InvalidInput" && path !== "Fault" && path !== "Step")
        .map(lowerFirst),
    ),
  );
});
