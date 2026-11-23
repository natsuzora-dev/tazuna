import { readdirSync } from "node:fs";
import { join } from "node:path";
import { Converter } from "../../src/convert/program.ts";
import type { Spec } from "../../src/load/load.ts";
import { folders, loadedSpec } from "../fixtures/fixtures.ts";

/**
 * The examples of lowered scenarios, which the engine's test request runs: test/unit/simulate/<example>/, each a spec and pairs of
 * <name>.scenario.json, a lowered scenario, and <name>.expected.json, the outcome.
 */
export const simRoot = join(import.meta.dirname, "simulate");

/**
 * Loads the spec of the example `root` with its functions converted to IR, without the checks that an example may
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

/** Returns the examples, each with the names of its scenario files. */
export const simExamples = (): { readonly root: string; readonly scenarios: readonly string[] }[] =>
  folders(simRoot).map((root) => ({
    root,
    scenarios: readdirSync(root)
      .filter((name) => name.endsWith(scenarioSuffix))
      .map((name) => name.slice(0, -scenarioSuffix.length))
      .sort(),
  }));
