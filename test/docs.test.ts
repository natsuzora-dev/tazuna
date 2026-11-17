import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { leanRoot } from "./examples.ts";

const root = join(import.meta.dirname, "..");
const read = (path: string) => readFileSync(join(root, path), "utf8");
const docs = ["README.md", "docs/guarantees.md", "docs/writing-specs.md"].map((path) => ({ path, text: read(path) }));
const guarantees = read("docs/guarantees.md");

const leanText = readdirSync(leanRoot, { recursive: true, encoding: "utf8" })
  .filter((f) => f.endsWith(".lean"))
  .map((f) => readFileSync(join(leanRoot, f), "utf8"))
  .join("\n");

const groups = [...read("src/data/violation.ts").matchAll(/^ {2}\| "(\w+)"/gm)].map((m) => m[1] ?? "");

test("Each theorem that docs/guarantees.md names under Proven properties is a theorem of lean/Tazuna", () => {
  const section = guarantees.slice(guarantees.indexOf("## Proven properties"));
  const names = [...section.matchAll(/\((`[\w.]+`(?:, `[\w.]+`)*)\)/g)].flatMap((m) =>
    [...(m[1] ?? "").matchAll(/`([^`]+)`/g)].map((n) => n[1] ?? ""),
  );
  assert.ok(names.length > 0);
  const declared = (name: string) => new RegExp(`theorem ${name.replaceAll(".", "\\.")}[\\s(:{]`).test(leanText);
  assert.deepEqual(
    names.filter((n) => !declared(n)),
    [],
  );
});

test("Each violation kind that a doc names is a kind of its group", () => {
  const groupSource = (group: string) => {
    const base = join(root, "src/data", group.charAt(0).toLowerCase() + group.slice(1));
    return existsSync(`${base}.generated.ts`)
      ? readFileSync(`${base}.generated.ts`, "utf8")
      : readFileSync(`${base}.ts`, "utf8");
  };
  const unknown = docs.flatMap(({ path, text }) =>
    [...text.matchAll(/`(\w+)\.(\w+)`/g)]
      .filter(([, group = ""]) => groups.includes(group))
      .filter(([, group = "", kind = ""]) => !new RegExp(`\\b${kind}\\b`).test(groupSource(group)))
      .map(([kind]) => `${path} ${kind}`),
  );
  assert.deepEqual(unknown, []);
});

test("The table of who fixes a violation in docs/guarantees.md has one row per group", () => {
  const table = guarantees.slice(guarantees.indexOf("## Who fixes a violation"), guarantees.indexOf("## Detections"));
  const rows = [...table.matchAll(/^\| `(\w+)` \|/gm)].map((m) => m[1]);
  assert.deepEqual(rows.toSorted(), groups.toSorted());
});
