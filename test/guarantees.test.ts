import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { leanRoot } from "./examples.ts";
import { guarantees } from "./guarantees.generated.ts";

const tests = import.meta.dirname;

/** The names in `a` that `b` lacks, and the names in `b` that `a` lacks. */
const difference = (a: readonly string[], b: readonly string[]) => ({
  onlyFirst: a.filter((n) => !b.includes(n)).toSorted(),
  onlySecond: b.filter((n) => !a.includes(n)).toSorted(),
});
const none = { onlyFirst: [], onlySecond: [] };

test("The theorems that docs/guarantees.md cites are the theorems tagged @[guarantee], and no others", () => {
  const doc = readFileSync(join(tests, "../docs/guarantees.md"), "utf8");
  const cited = [...new Set([...doc.matchAll(/`([a-z][A-Za-z0-9]*_\w*)`/g)].map((m) => m[1] ?? ""))];
  assert.deepEqual(difference(cited, guarantees), none);
});

test("The theorems tagged @[guarantee] in lean/Tazuna/Thm are those that test/guarantees.generated.ts lists", () => {
  const tagged = readdirSync(join(leanRoot, "Thm"), { recursive: true, encoding: "utf8" })
    .filter((file) => file.endsWith(".lean"))
    .flatMap((file) =>
      [
        ...readFileSync(join(leanRoot, "Thm", file), "utf8")
          .replace(/\/-[\s\S]*?-\//g, "")
          .replace(/--.*$/gm, "")
          .matchAll(/@\[[^\]]*\bguarantee\b[^\]]*\]\s*theorem\s+([^\s(:{[]+)/g),
      ].map((m) => m[1] ?? ""),
    );
  assert.deepEqual(difference(tagged, guarantees), none);
});
