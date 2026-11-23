import assert from "node:assert/strict";
import { join } from "node:path";
import { test } from "node:test";
import { ask } from "../../src/cli/engine.ts";
import { InternalError } from "../../src/data/internalError.ts";
import type { Structure } from "../../src/spec/structure.generated.ts";
import { convertedSpec } from "./simulate.ts";

const fixtures = join(import.meta.dirname, "../fixtures/prove/counterexample");
const root = join(fixtures, "second-record");

test("prove stops with an internal error, never a proof, when the solver answers fewer scripts than it asked", async () => {
  const { structure } = await convertedSpec(root);
  const [queried] = ask("proveQueries", [{ structure }]);
  assert.ok(queried !== undefined && queried.scripts.length > 1);
  const unsat = queried.scripts.map(() => "unsat");
  const [proved] = ask("prove", [{ structure, answers: unsat }]);
  assert.ok(proved?.results.every((r) => r.verdict.kind === "proved"));
  assert.throws(() => ask("prove", [{ structure, answers: unsat.slice(1) }]), InternalError);
  assert.throws(() => ask("prove", [{ structure, answers: [] }]), InternalError);
});

const withoutEntries = (structure: Structure, callback: "ensures" | "responseExpect"): Structure => ({
  ...structure,
  program: { ...structure.program, [callback]: [] },
});

test("prove stops with an internal error, never a proof, when the program lacks a body that the structure names", async () => {
  const missed = (await convertedSpec(join(fixtures, "missed-response"))).structure;
  assert.throws(() => ask("proveQueries", [{ structure: withoutEntries(missed, "responseExpect") }]), InternalError);
  const ensures = (await convertedSpec(join(fixtures, "command-ensures"))).structure;
  assert.throws(() => ask("proveQueries", [{ structure: withoutEntries(ensures, "ensures") }]), InternalError);
});
