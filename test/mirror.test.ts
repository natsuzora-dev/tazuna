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

const tsPaths = (folder: string) =>
  readdirSync(join(import.meta.dirname, "../src", folder), { recursive: true, encoding: "utf8" })
    .filter((file) => file.endsWith(".ts"))
    .map((file) => file.slice(0, -".ts".length));

test("The .ts paths under src/service are the .lean paths under lean/Tazuna/Service with a lowercase first letter in each part (chart/exit.ts for Chart/Exit.lean), except InvalidInput.lean, Fault.lean, and Step.lean, which generate TS types in src/data", () => {
  assert.deepEqual(
    new Set(tsPaths("service")),
    new Set(
      leanModulePaths("Service")
        .filter((path) => !["InvalidInput", "Fault", "Step"].includes(path))
        .map(lowerFirst),
    ),
  );
});

test("The .ts paths under src/sim are the .lean paths under lean/Tazuna/Sim with a lowercase first letter, except Network.lean, which only proofs use", () => {
  assert.deepEqual(
    new Set(tsPaths("sim")),
    new Set(
      leanModulePaths("Sim")
        .filter((path) => path !== "Network")
        .map(lowerFirst),
    ),
  );
});
