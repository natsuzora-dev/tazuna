import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { join, sep } from "node:path";
import { test } from "node:test";

const leanRoot = join(import.meta.dirname, "../../lean/Tazuna");

/** Returns the paths of the Lean modules relative to Tazuna/<folder>, such as Chart/Always in Service. */
const leanModulePaths = (folder: string): string[] =>
  readdirSync(join(leanRoot, folder), { recursive: true, encoding: "utf8" })
    .filter((file) => file.endsWith(".lean"))
    .map((file) => file.slice(0, -".lean".length))
    .sort();

/** Returns the paths relative to Tazuna of the Lean modules outside Thm, such as Service/Chart/Always. */
const leanDefinitionPaths = (): string[] => leanModulePaths("").filter((path) => !path.startsWith("Thm/"));

const source = (folder: string, path: string) => readFileSync(join(leanRoot, folder, `${path}.lean`), "utf8");

/** For each folder, the folders under Tazuna whose modules its files may import. */
const allowedImports: Readonly<Record<string, readonly string[]>> = {
  Data: ["Data"],
  // The structure holds the program, whose IR names only data and the definitions of Spec.
  Spec: ["Data", "Spec", "Ir/Expr"],
  Validation: ["Data", "Spec", "Validation"],
  Service: ["Data", "Spec", "Service"],
  Scenario: ["Data", "Spec", "Scenario"],
  Sim: ["Data", "Spec", "Service", "Scenario", "Sim"],
  Explore: ["Data", "Spec", "Service", "Scenario", "Sim", "Explore"],
  Verify: ["Data", "Spec", "Verify"],
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

test("Each file outside Thm opens only Tazuna and the namespaces under its folder (Tazuna.Service.* for Service/Basic.lean)", () => {
  const outside = leanDefinitionPaths().flatMap((path) => {
    const folder = path.split(sep)[0] ?? "";
    const open: string[] = [];
    const found: string[] = [];
    for (const [, keyword, name = ""] of source("", path).matchAll(/^(namespace|end) (\S+)$/gm))
      if (keyword === "namespace") {
        open.push(name);
        found.push(open.join("."));
      } else if (open.at(-1) === name) open.pop();
    return found
      .filter((n) => n !== "Tazuna" && n !== `Tazuna.${folder}` && !n.startsWith(`Tazuna.${folder}.`))
      .map((n) => `${path}.lean ${n}`);
  });
  assert.deepEqual(outside, []);
});

test("Each Validation file except the violation types has a file of the same name in Thm/Validation, and the other way around", () => {
  assert.deepEqual(
    leanModulePaths("Validation").filter((path) => path !== "Illegal" && path !== "NonCanonical"),
    leanModulePaths("Thm/Validation"),
  );
});
