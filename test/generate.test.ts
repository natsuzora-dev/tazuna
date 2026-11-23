import assert from "node:assert/strict";
import { mkdtempSync, readdirSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, join, relative } from "node:path";
import { test } from "node:test";
import { folders } from "./examples.ts";
import { expected, generateLinesOf } from "./expected.ts";

const generateRoot = join(import.meta.dirname, "generate");

const outcomes = ["reached", "notReached", "unreachable", "notEncodable"] as const;

const jsonl = (lines: readonly string[]) => lines.map((line) => `${line}\n`).join("");

/** The files under `folder`, at any depth, relative to it, in name order. */
const filesUnder = (folder: string): string[] =>
  readdirSync(folder, { recursive: true, withFileTypes: true })
    .filter((e) => e.isFile())
    .map((e) => relative(folder, join(e.parentPath, e.name)))
    .sort();

test("The folder names directly under test/generate are the outcomes of generate", () => {
  assert.deepEqual(new Set(folders(generateRoot).map((folder) => basename(folder))), new Set(outcomes));
});

for (const outcome of outcomes)
  for (const example of folders(join(generateRoot, outcome)))
    test(relative(import.meta.dirname, example), async (t) => {
      const out = mkdtempSync(join(tmpdir(), "tazuna-generate-"));
      try {
        const { lines, code } = await generateLinesOf(example, out);
        assert.equal(code, 0);
        t.assert.fileSnapshot(lines, join(example, expected), { serializers: [jsonl] });
        assert.ok(lines.some((line) => (JSON.parse(line) as { outcome: { kind: string } }).outcome.kind === outcome));
        const written = filesUnder(out);
        for (const file of written)
          t.assert.fileSnapshot(readFileSync(join(out, file), "utf8"), join(example, "inputs", file), {
            serializers: [String],
          });
        assert.deepEqual(filesUnder(join(example, "inputs")), written);
      } finally {
        rmSync(out, { recursive: true, force: true });
      }
    });
