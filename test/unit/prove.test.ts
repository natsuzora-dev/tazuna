import assert from "node:assert/strict";
import { join } from "node:path";
import { test } from "node:test";
import { converse } from "../../src/cli/engine.ts";
import { InternalError } from "../../src/data/internalError.ts";
import type { Structure } from "../../src/spec/structure.generated.ts";
import { convertedSpec } from "./simulate.ts";

const fixtures = join(import.meta.dirname, "../fixtures/prove/counterexample");
const root = join(fixtures, "second-record");

test("prove stops with an internal error, never a proof, when the solver answers fewer scripts than it asked", async () => {
  const { structure } = await convertedSpec(root);
  const unsat = async (scripts: readonly string[]) => {
    assert.ok(scripts.length > 1);
    return scripts.map(() => "unsat");
  };
  const proved = await converse("prove", { structure }, unsat);
  assert.ok(proved.results.every((r) => r.verdict.kind === "proved"));
  const short = async (scripts: readonly string[]) => (await unsat(scripts)).slice(1);
  await assert.rejects(converse("prove", { structure }, short), InternalError);
  await assert.rejects(
    converse("prove", { structure }, async () => []),
    InternalError,
  );
});

const withoutEntries = (structure: Structure, callback: "ensures" | "responseExpect"): Structure => ({
  ...structure,
  program: { ...structure.program, [callback]: [] },
});

test("prove stops with an internal error, never a proof, when the program lacks a body that the structure names", async () => {
  const missed = (await convertedSpec(join(fixtures, "missed-response"))).structure;
  const solve = async (scripts: readonly string[]) => scripts.map(() => "unsat");
  await assert.rejects(
    converse("prove", { structure: withoutEntries(missed, "responseExpect") }, solve),
    InternalError,
  );
  const ensures = (await convertedSpec(join(fixtures, "command-ensures"))).structure;
  await assert.rejects(converse("prove", { structure: withoutEntries(ensures, "ensures") }, solve), InternalError);
});
