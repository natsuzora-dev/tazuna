import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { explanations } from "../scripts/explain.ts";
import { explain, explanationsPath } from "../src/cli/explain.ts";
import { kinds } from "../src/data/kinds.ts";
import { unexemplified } from "./kinds.ts";

const maxExcerptLines = 40;
const built = explanations();
const kindEntries = kinds.map((kind) => [kind, built.kinds[kind]] as const);

test("explain.json is what scripts/explain.ts builds", () => {
  assert.deepEqual(JSON.parse(readFileSync(explanationsPath, "utf8")), built);
});

test("Each group and each kind has a doc comment", () => {
  assert.deepEqual(
    Object.entries(built.groups).filter(([, doc]) => doc === ""),
    [],
  );
  assert.deepEqual(
    kindEntries.filter(([, k]) => k.meaning === ""),
    [],
  );
});

test(`Each kind has an example whose excerpt has at most ${maxExcerptLines} lines and holds the reported line, except the unexemplified kinds`, () => {
  assert.deepEqual(
    kindEntries
      .filter(([kind, k]) => (unexemplified[kind] !== undefined) === (k.example !== undefined))
      .map(([kind]) => kind),
    [],
  );
  assert.deepEqual(
    kindEntries
      .flatMap(([kind, k]) => (k.example?.excerpt === undefined ? [] : [{ kind, ...k.example.excerpt }]))
      .filter(({ from, to, line }) => to - from >= maxExcerptLines || line < from || line > to)
      .map(({ kind }) => kind),
    [],
  );
});

test("An example of a kind reported only inside a ChoiceDependent difference shows the nested violation and names the kind that holds it", () => {
  const nested = kindEntries.filter(([, k]) => k.example?.within !== undefined);
  assert.ok(nested.length > 0);
  for (const [kind, k] of nested) {
    assert.equal((JSON.parse(k.example?.violation ?? "{}") as { kind?: string }).kind, kind);
    const explained = explain(kind);
    assert.ok("markdown" in explained && explained.markdown.includes(`of a \`${k.example?.within}\` violation:`), kind);
  }
});

test("explain marks the reported line of the excerpt, and names an unknown kind and a missing explain.json as misuses", () => {
  const explained = explain("Fault.failedEnsures");
  assert.ok("markdown" in explained);
  const excerpt = built.kinds["Fault.failedEnsures"].example?.excerpt;
  assert.ok(excerpt !== undefined);
  assert.match(explained.markdown, new RegExp(`^> +${excerpt.line} \\| `, "m"));
  assert.deepEqual(explain("Fault.data"), { misuse: "unknown kind Fault.data" });
  assert.deepEqual(explain("constructor"), { misuse: "unknown kind constructor" });
  assert.deepEqual(explain("Fault.failedEnsures", "/missing/explain.json"), {
    misuse: "/missing/explain.json is missing. Reinstall tazuna",
  });
});
