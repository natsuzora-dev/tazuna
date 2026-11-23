import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { enginePlatforms } from "../../src/cli/engine.ts";

const read = (path: string) =>
  JSON.parse(readFileSync(join(import.meta.dirname, "../..", path), "utf8")) as {
    readonly name: string;
    readonly version: string;
    readonly optionalDependencies?: Readonly<Record<string, string>>;
  };

test("tazuna depends on the engine package of each platform at its own exact version", () => {
  const tazuna = read("package.json");
  const engines = enginePlatforms.map((platform) => read(`npm/${platform}/package.json`));
  assert.deepEqual(
    tazuna.optionalDependencies,
    Object.fromEntries(engines.map((engine) => [engine.name, tazuna.version])),
  );
  assert.deepEqual(new Set(engines.map((engine) => engine.version)), new Set([tazuna.version]));
});

test("the engine workflow builds the engine of each platform", () => {
  const workflow = readFileSync(join(import.meta.dirname, "../../.github/workflows/engine.yml"), "utf8");
  assert.deepEqual([...workflow.matchAll(/platform: ([\w-]+),/g)].map((m) => m[1]).sort(), [...enginePlatforms].sort());
});
