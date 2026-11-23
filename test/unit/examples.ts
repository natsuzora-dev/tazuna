import { readdirSync } from "node:fs";
import { join } from "node:path";
import { Converter } from "../../src/convert/program.ts";
import type { Spec } from "../../src/load/load.ts";
import { folders, loadedSpec } from "../fixtures/fixtures.ts";

export const simRoot = join(import.meta.dirname, "sim");
export const leanRoot = join(import.meta.dirname, "../../lean/Tazuna");

/** Returns the paths of the Lean modules relative to Tazuna/<folder>, such as Chart/Always in Service. */
export const leanModulePaths = (folder: string): string[] =>
  readdirSync(join(leanRoot, folder), { recursive: true, encoding: "utf8" })
    .filter((file) => file.endsWith(".lean"))
    .map((file) => file.slice(0, -".lean".length))
    .sort();

/** Returns the paths relative to Tazuna of the Lean modules outside Thm, such as Service/Chart/Always. */
export const leanDefinitionPaths = (): string[] => leanModulePaths("").filter((path) => !path.startsWith("Thm/"));

const atPaths = (root: string, paths: readonly string[]): string[] =>
  paths.flatMap((path) => folders(join(root, path)));

/**
 * Loads the spec of the example `root` with its functions converted to IR, without the checks that a sim example may
 * fail on purpose, and throws when a function stays outside the IR.
 */
export async function convertedSpec(root: string): Promise<Spec> {
  const spec = await loadedSpec(root);
  const converter = new Converter();
  try {
    const { program, notConverted } = converter.program(spec);
    if (notConverted.length > 0) throw new Error(`${root}: ${notConverted.map((n) => n.reason).join(", ")}`);
    return { ...spec, structure: { ...spec.structure, program } };
  } finally {
    converter.close();
  }
}

export const scenarioSuffix = ".scenario.json";
export const outcomeSuffix = ".expected.json";

/** Returns the examples test/sim/<Lean Sim module path>/<example>/, each with the names of its scenario files. */
export const simExamples = (): { readonly root: string; readonly scenarios: readonly string[] }[] =>
  atPaths(simRoot, leanModulePaths("Sim")).map((root) => ({
    root,
    scenarios: readdirSync(root)
      .filter((name) => name.endsWith(scenarioSuffix))
      .map((name) => name.slice(0, -scenarioSuffix.length))
      .sort(),
  }));
