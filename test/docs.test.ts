import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { groups as groupInfos } from "../src/data/groups.ts";
import { leanRoot } from "./examples.ts";

const root = join(import.meta.dirname, "..");
const read = (path: string) => readFileSync(join(root, path), "utf8");
const docs = ["README.md", "docs/guarantees.md", "docs/concepts.md"].map((path) => ({ path, text: read(path) }));
const guarantees = read("docs/guarantees.md");

/** The declarations of lean/Tazuna outside comments: each name as written, its keyword, and its file. */
const declarations = readdirSync(leanRoot, { recursive: true, encoding: "utf8" })
  .filter((file) => file.endsWith(".lean"))
  .flatMap((file) => {
    const code = readFileSync(join(leanRoot, file), "utf8")
      .replace(/\/-[\s\S]*?-\//g, "")
      .replace(/--.*$/gm, "");
    return [
      ...code.matchAll(
        /^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*(theorem|def|abbrev|structure|inductive)\s+([^\s(:{[]+)/gm,
      ),
    ].map(([, keyword = "", name = ""]) => ({ keyword, name, file: `lean/Tazuna/${file}` }));
  });
const isTheorem = (name: string) =>
  declarations.some((d) => d.keyword === "theorem" && d.name === name && d.file.startsWith("lean/Tazuna/Thm/"));

const groups = [...read("src/data/violation.ts").matchAll(/^ {2}\| "(\w+)"/gm)].map((m) => m[1] ?? "");

const proven = guarantees.slice(guarantees.indexOf("## Proven properties"));
const namesIn = (list: string) => [...list.matchAll(/`([^`]+)`/g)].map((n) => n[1] ?? "");
/** The last cell of each body row of the tables under Proven properties: the theorems that prove the row. */
const theoremCells = proven
  .split("\n")
  .filter((line) => line.startsWith("| ") && !line.startsWith("| Property |"))
  .map((line) => line.slice(0, -" |".length).split(" | ").at(-1) ?? "");

test("Proven properties is the last section of docs/guarantees.md, and each of its rows cites the theorems that prove it", () => {
  assert.ok(!proven.includes("\n## "));
  assert.ok(theoremCells.length > 0);
  assert.deepEqual(
    theoremCells.filter((cell) => !/^`[\w.]+`(?:, `[\w.]+`)*$/.test(cell)),
    [],
  );
});

test("Each theorem that a doc cites is a theorem stated in lean/Tazuna/Thm: every name in a Theorems cell under Proven properties, and every name with an underscore elsewhere", () => {
  const cited = [
    ...theoremCells.flatMap(namesIn),
    ...docs.flatMap(({ text }) => [...text.matchAll(/`([a-z][A-Za-z0-9]*_\w*)`/g)].map((m) => m[1] ?? "")),
  ];
  assert.ok(cited.length > 0);
  assert.deepEqual(
    [...new Set(cited)].filter((name) => !isTheorem(name)),
    [],
  );
});

test("Each Lean name that a doc cites with its files is declared in each of them, in its namespace or not", () => {
  const cited = docs.flatMap(({ text }) =>
    [...text.matchAll(/`([\w.]+)` in ((?:`lean\/[\w/]+\.lean`(?:,? and |, )?)+)/g)].flatMap(
      ([, name = "", files = ""]) => namesIn(files).map((file) => ({ name, file })),
    ),
  );
  assert.ok(cited.length > 0);
  assert.deepEqual(
    cited.filter(
      ({ name, file }) =>
        !declarations.some((d) => (d.name === name || d.name.endsWith(`.${name}`)) && d.file === file),
    ),
    [],
  );
});

const groupSource = (group: string) => {
  const base = join(root, "src/data", group.charAt(0).toLowerCase() + group.slice(1));
  return existsSync(`${base}.generated.ts`)
    ? readFileSync(`${base}.generated.ts`, "utf8")
    : readFileSync(`${base}.ts`, "utf8");
};
const unknownKinds = (path: string, text: string, pattern: RegExp) =>
  [...text.matchAll(pattern)]
    .filter(([, group = ""]) => groups.includes(group))
    .filter(([, group = "", kind = ""]) => !new RegExp(`\\b${kind}\\b`).test(groupSource(group)))
    .map(([kind]) => `${path} ${kind}`);

test("Each violation kind that a doc names is a kind of its group", () => {
  assert.deepEqual(
    docs.flatMap(({ path, text }) => unknownKinds(path, text, /`(\w+)\.(\w+)`/g)),
    [],
  );
});

test("Each violation kind that a doc comment in src names is a kind of its group", () => {
  const comments = (text: string) => [...text.matchAll(/\/\*\*[\s\S]*?\*\//g)].map((m) => m[0]).join("\n");
  const unknown = readdirSync(join(root, "src"), { recursive: true, encoding: "utf8" })
    .filter((f) => f.endsWith(".ts"))
    .flatMap((f) => unknownKinds(`src/${f}`, comments(read(`src/${f}`)), /\b([A-Z]\w+)\.(\w+)\b/g));
  assert.deepEqual(unknown, []);
});

test("The table of who fixes a violation in docs/guarantees.md has one row per group of src/data/groups.ts, in its order and with its reportedBy and fixedIn", () => {
  const table = guarantees.slice(guarantees.indexOf("## Who fixes a violation"), guarantees.indexOf("## Detections"));
  const rows = table.split("\n").filter((line) => line.startsWith("| `"));
  assert.deepEqual(
    rows,
    Object.entries(groupInfos).map(
      ([group, { reportedBy, fixedIn }]) =>
        `| \`${group}\` | ${reportedBy.map((c) => `\`${c}\``).join(", ")} | ${fixedIn} |`,
    ),
  );
});
