import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { parseSync } from "oxc-parser";

const src = join(import.meta.dirname, "../../src");

function documentedNames(file: string): Set<string> {
  const text = readFileSync(join(src, file), "utf8");
  const { program, comments } = parseSync(file, text);
  const jsdocEnds = new Set(comments.filter((c) => c.type === "Block" && c.value.startsWith("*")).map((c) => c.end));
  // Line comments such as biome-ignore may sit between the JSDoc and the declaration.
  const hasJsdoc = (start: number) => {
    let before = text.slice(0, start).trimEnd();
    while (before.split("\n").at(-1)?.trimStart().startsWith("//"))
      before = before.slice(0, before.lastIndexOf("\n")).trimEnd();
    return jsdocEnds.has(before.length);
  };
  const names = new Set<string>();
  for (const statement of program.body) {
    const declaration = statement.type === "ExportNamedDeclaration" ? statement.declaration : statement;
    if (declaration === null || declaration === undefined) continue;
    const start = statement.start;
    if (declaration.type === "VariableDeclaration") {
      for (const d of declaration.declarations) if (d.id.type === "Identifier" && hasJsdoc(start)) names.add(d.id.name);
    } else if ("id" in declaration && declaration.id?.type === "Identifier" && hasJsdoc(start))
      names.add(declaration.id.name);
  }
  return names;
}

test("Every name that tazuna exports has a JSDoc", () => {
  const index = parseSync("index.ts", readFileSync(join(src, "index.ts"), "utf8")).program;
  const required = index.body.flatMap((s) =>
    s.type === "ExportNamedDeclaration" && s.source !== null
      ? s.specifiers.map((x) => ({
          file: s.source?.value.replace("./", "") ?? "",
          name: String(x.local.type === "Identifier" ? x.local.name : x.local.value),
        }))
      : [],
  );
  assert.deepEqual(
    required.filter(({ file, name }) => !documentedNames(file).has(name)).map(({ file, name }) => `${file} ${name}`),
    [],
  );
});
