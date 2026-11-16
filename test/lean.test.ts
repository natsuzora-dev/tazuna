import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join, sep } from "node:path";
import { test } from "node:test";
import { leanModulePaths, leanRoot } from "./examples.ts";

const source = (folder: string, path: string) => readFileSync(join(leanRoot, folder, `${path}.lean`), "utf8");

/** For each folder, the folders under Tazuna whose modules its files may import. */
const allowedImports: Readonly<Record<string, readonly string[]>> = {
  Data: ["Data"],
  Syntax: ["Data", "Syntax"],
  Validation: ["Data", "Syntax", "Validation"],
  Service: ["Data", "Syntax", "Service"],
  Scenario: ["Data", "Syntax", "Scenario"],
  Sim: ["Data", "Syntax", "Service", "Scenario", "Sim"],
  Observe: ["Data", "Syntax", "Service", "Observe"],
  Verify: ["Data", "Syntax", "Verify"],
};

for (const [folder, allowed] of Object.entries(allowedImports))
  test(`The files of ${folder} import only the Tazuna modules of ${allowed.join(", ")}`, () => {
    const outside = leanModulePaths(folder).flatMap((path) =>
      [...source(folder, path).matchAll(/^import Tazuna\.(\S+)$/gm)]
        .map((m) => (m[1] ?? "").split(".").join("/"))
        .filter((path) => !allowed.some((a) => path === a || path.startsWith(`${a}/`))),
    );
    assert.deepEqual(outside, []);
  });

test("The namespace of each Thm file is its path (Tazuna.Thm.Service.Chart.Exit for Tazuna/Thm/Service/Chart/Exit.lean)", () => {
  for (const path of leanModulePaths("Thm")) {
    const expected = `Tazuna.Thm.${path.split(sep).join(".")}`;
    const namespaces = [...source("Thm", path).matchAll(/^namespace (\S+)$/gm)].map((m) => m[1]);
    assert.deepEqual([...new Set(namespaces)], [expected], `Thm/${path}.lean`);
  }
});

test("Each Validation file except Check.lean and Illegal.lean has a file of the same name in Thm/Validation, and the other way around", () => {
  assert.deepEqual(
    leanModulePaths("Validation").filter((path) => path !== "Check" && path !== "Illegal"),
    leanModulePaths("Thm/Validation"),
  );
});
