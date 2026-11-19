import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";

const root = join(import.meta.dirname, "..");

/** Each Biome plugin in biome.json, with expressions it reports and expressions it leaves alone. */
const examples: Record<string, { readonly reported: readonly string[]; readonly clean: readonly string[] }> = {
  "./lint/sameJson.grit": {
    reported: [
      "canonicalJson(a) === canonicalJson(b)",
      "JSON.stringify(a) !== JSON.stringify(b)",
      "canonicalJson(a) === JSON.stringify(b)",
      "JSON.stringify(a) != canonicalJson(b)",
      "canonicalJson(a) == canonicalJson(b)",
    ],
    clean: ["sameJson(a, b)", "canonicalJson(a) === key"],
  },
};

/** The lines of `expressions` that `plugin` reports, each expression written on its own line. */
function reportedLines(plugin: string, expressions: readonly string[]): number[] {
  const folder = mkdtempSync(join(tmpdir(), "tazuna-lint-"));
  try {
    writeFileSync(join(folder, "biome.json"), JSON.stringify({ plugins: [join(root, plugin)] }));
    writeFileSync(join(folder, "code.ts"), expressions.map((e, i) => `export const e${i} = ${e};\n`).join(""));
    let output: string;
    try {
      output = execFileSync(join(root, "node_modules/.bin/biome"), ["lint", "--reporter=json", "code.ts"], {
        cwd: folder,
        encoding: "utf8",
      });
    } catch (error) {
      output = (error as { stdout: string }).stdout;
    }
    const { diagnostics } = JSON.parse(output) as {
      diagnostics: { category: string; location: { start: { line: number } } }[];
    };
    return diagnostics.filter((d) => d.category === "plugin").map((d) => d.location.start.line);
  } finally {
    rmSync(folder, { recursive: true });
  }
}

test("Each Biome plugin in biome.json has examples here", () => {
  const { plugins } = JSON.parse(readFileSync(join(root, "biome.json"), "utf8")) as { plugins: string[] };
  assert.deepEqual(plugins, Object.keys(examples));
});

for (const [plugin, { reported, clean }] of Object.entries(examples))
  test(`${plugin} reports each reported example and no clean one`, () => {
    assert.deepEqual(
      reportedLines(plugin, [...reported, ...clean]),
      reported.map((_, i) => i + 1),
    );
  });
