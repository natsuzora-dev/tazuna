import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { dirname, join, relative, resolve } from "node:path";
import { test } from "node:test";
import { main } from "../src/cli/main.ts";
import { allKinds } from "./kinds.ts";

const root = join(import.meta.dirname, "..");
const files: readonly string[] = JSON.parse(readFileSync(join(root, "package.json"), "utf8")).files;
const skills = readdirSync(join(root, "skills")).map((name) => {
  const path = join(root, "skills", name, "SKILL.md");
  return { name, path, text: readFileSync(path, "utf8") };
});

/** Whether the package's `files` include a path relative to the package root: a negated entry excludes, `*` matches within a folder. */
const packed = (path: string) => {
  const matches = (entry: string) => {
    const pattern = new RegExp(`^${entry.replace(/[.]/g, "\\.").replace(/\*/g, "[^/]*")}(?:/|$)`);
    return pattern.test(path);
  };
  return (
    files.some((entry) => !entry.startsWith("!") && matches(entry)) &&
    !files.some((entry) => entry.startsWith("!") && matches(entry.slice(1)))
  );
};

const help = async () => {
  const out: string[] = [];
  await main(["--help"], { cwd: root, log: (line) => out.push(line), error: () => {} });
  return out.join("\n");
};

test("The package files include the skills, the ToDo sample spec, and the docs", () => {
  for (const path of [
    "skills/tazuna/SKILL.md",
    "samples/todo/spec/todo/scenarios.ts",
    "docs/concepts.md",
    "docs/guarantees.md",
  ])
    assert.ok(packed(path), path);
  assert.ok(!packed("samples/todo/web/package.json"));
});

test("Each skill has the frontmatter name of its folder and a description", () => {
  assert.ok(skills.length > 0);
  for (const { name, text } of skills) {
    assert.match(text, new RegExp(`^---\\nname: ${name}\\ndescription: \\S`));
  }
});

test("Each link in a skill resolves to a packed file or folder of the package", () => {
  for (const { path, text } of skills) {
    const links = [...text.matchAll(/\]\(([^)]+)\)/g)].map((m) => m[1] ?? "");
    assert.ok(links.length > 0);
    for (const link of links) {
      const target = relative(root, resolve(dirname(path), link));
      assert.ok(existsSync(join(root, target)) && packed(target), `${link} from ${path}`);
    }
  }
});

test("Each command, option, and violation kind that a skill names exists", async () => {
  const usage = await help();
  for (const { text } of skills) {
    const commands = [...text.matchAll(/`npx tazuna (\w+)/g)].map((m) => m[1] ?? "");
    const options = [...text.matchAll(/(?<![\w-])(--[a-z]+)/g)].map((m) => m[1] ?? "");
    const kinds = [...text.matchAll(/`([A-Z]\w+)(?:\.(\w+))?`/g)].map(([, group = "", kind]) =>
      kind === undefined ? group : `${group}.${kind}`,
    );
    assert.ok(commands.length > 0 && options.length > 0 && kinds.length > 0);
    for (const command of commands) assert.match(usage, new RegExp(`^ {2}${command} `, "m"), command);
    for (const option of options) assert.match(usage, new RegExp(`^ {4}${option}\\b`, "m"), option);
    for (const kind of kinds)
      assert.ok(allKinds.includes(kind) || allKinds.some((k) => k.startsWith(`${kind}.`)), kind);
  }
});
