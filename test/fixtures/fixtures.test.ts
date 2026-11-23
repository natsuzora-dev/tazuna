import assert from "node:assert/strict";
import { existsSync, mkdtempSync, readdirSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, join, relative } from "node:path";
import { type TestContext, test } from "node:test";
import type { ProveLine } from "../../src/cli/prove.ts";
import { groups } from "../../src/data/groups.ts";
import { type Group, parseKind } from "../../src/data/kinds.ts";
import { sameJson } from "../../src/data/values.ts";
import type { ReportedViolation } from "../../src/data/violation.ts";
import {
  type Command,
  expected,
  fixtures,
  fixturesRoot,
  folders,
  isServiceFolder,
  kinds,
  maskedStack,
  noViolations,
  run,
} from "./fixtures.ts";

const jsonl = (lines: readonly string[]) => lines.map((line) => `${line}\n`).join("");

/** The folders under test/fixtures/<command> that are no kind, each with what it holds. */
const helpers: Partial<Record<Command, Readonly<Record<string, string>>>> = {
  check: { outside: "the modules that Restricted/imported-module imports from outside its spec" },
  prove: {
    assumes: "the cases with a proof that assumes a property which prove does not prove, so their verdicts mix",
  },
};

const commands = Object.keys(kinds) as Command[];

test("The folders under test/fixtures are the commands, and those under each command are its kinds, each with a case", () => {
  assert.deepEqual(
    folders(fixturesRoot).map((f) => basename(f)),
    commands.toSorted(),
  );
  for (const command of commands) {
    const named = folders(join(fixturesRoot, command)).map((f) => basename(f));
    const kindsOf: readonly string[] = kinds[command];
    assert.deepEqual(
      named.filter((name) => !kindsOf.includes(name) && helpers[command]?.[name] === undefined),
      [],
      command,
    );
    assert.deepEqual(
      named.filter((name) => kindsOf.includes(name) && fixtures(command, name).length === 0),
      [],
      command,
    );
  }
});

test("Every verdict of prove and every outcome of generate has a fixture", () => {
  for (const command of ["prove", "generate"] as const)
    assert.deepEqual(
      kinds[command].filter((kind) => fixtures(command, kind).length === 0),
      [],
    );
});

test("Each case of test holds only service folders and expected.jsonl", () => {
  for (const kind of kinds.test)
    for (const root of fixtures("test", kind))
      for (const entry of readdirSync(root, { withFileTypes: true }))
        assert.ok(
          entry.isDirectory() ? isServiceFolder(join(root, entry.name)) : entry.name === expected,
          relative(fixturesRoot, join(root, entry.name)),
        );
});

/** The arguments of the violation commands, run in the case's folder. */
function argsOf(command: "check" | "test" | "verify", kind: string): readonly string[] {
  if (command !== "verify") return [command, "."];
  const coverage = kind !== noViolations && !groups[kind as Group].reportedBy.some((c: string) => c === "verify");
  return ["verify", ".", "traces", ...(coverage ? ["--coverage"] : [])];
}

async function violationsTest(t: TestContext, command: "check" | "test" | "verify", kind: string, root: string) {
  const args = argsOf(command, kind);
  const { lines } = await run(root, args);
  const reportedBy = args.includes("--coverage") ? "verify --coverage" : command;
  const violations = lines.map((line) => JSON.parse(line) as ReportedViolation);
  for (const v of violations) {
    const group = parseKind(v.kind)?.group;
    assert.ok(group !== undefined && groups[group].reportedBy.some((c: string) => c === reportedBy), v.kind);
  }
  t.assert.fileSnapshot(
    violations.map((v) => JSON.stringify(maskedStack(v))),
    join(root, expected),
    { serializers: [jsonl] },
  );
  assert.deepEqual(
    violations.map((v) => v.kind).filter((k) => !k.startsWith(`${kind}.`)),
    [],
  );
}

for (const command of ["check", "test", "verify"] as const)
  for (const kind of kinds[command])
    for (const root of fixtures(command, kind))
      test(relative(fixturesRoot, root), (t) => violationsTest(t, command, kind, root));

/** The exit code of prove when every property has the verdict. */
const exitCodes = { proved: 0, counterexample: 1, undecided: 3 } as const;

for (const verdict of kinds.prove)
  for (const root of fixtures("prove", verdict))
    test(relative(fixturesRoot, root), async (t) => {
      const { lines, code } = await run(root, ["prove", "."]);
      assert.equal(code, exitCodes[verdict]);
      t.assert.fileSnapshot(lines, join(root, expected), { serializers: [jsonl] });
      assert.deepEqual(
        lines.map((line) => (JSON.parse(line) as { readonly verdict: { readonly kind: string } }).verdict.kind),
        lines.map(() => verdict),
      );
    });

for (const root of folders(join(fixturesRoot, "prove", "assumes")))
  test(relative(fixturesRoot, root), async (t) => {
    const { lines } = await run(root, ["prove", "."]);
    t.assert.fileSnapshot(lines, join(root, expected), { serializers: [jsonl] });
    const results = lines.map((line) => JSON.parse(line) as ProveLine);
    const proved = (p: unknown) => results.some((r) => sameJson(r.property, p) && r.verdict.kind === "proved");
    assert.ok(results.some((r) => r.verdict.kind === "proved" && r.assumes.length > 0));
    for (const r of results)
      for (const a of r.assumes) if (a.kind === "unproved") assert.ok(!proved(a.property), JSON.stringify(a.property));
  });

/** The files under `folder`, at any depth, relative to it, in name order, none when it is missing. */
const filesUnder = (folder: string): string[] =>
  (existsSync(folder) ? readdirSync(folder, { recursive: true, withFileTypes: true }) : [])
    .filter((e) => e.isFile())
    .map((e) => relative(folder, join(e.parentPath, e.name)))
    .sort();

for (const outcome of kinds.generate)
  for (const root of fixtures("generate", outcome))
    test(relative(fixturesRoot, root), async (t) => {
      const out = mkdtempSync(join(tmpdir(), "tazuna-generate-"));
      try {
        const { lines, code } = await run(root, ["generate", ".", out]);
        assert.equal(code, 0);
        t.assert.fileSnapshot(lines, join(root, expected), { serializers: [jsonl] });
        assert.ok(lines.some((line) => (JSON.parse(line) as { outcome: { kind: string } }).outcome.kind === outcome));
        const written = filesUnder(out);
        for (const file of written)
          t.assert.fileSnapshot(readFileSync(join(out, file), "utf8"), join(root, "inputs", file), {
            serializers: [String],
          });
        assert.deepEqual(filesUnder(join(root, "inputs")), written);
      } finally {
        rmSync(out, { recursive: true, force: true });
      }
    });
