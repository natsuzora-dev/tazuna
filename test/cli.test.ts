import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createServer } from "node:http";
import type { AddressInfo } from "node:net";
import { tmpdir } from "node:os";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { main } from "../src/cli/main.ts";
import { traceLine } from "../src/data/trace.generated.ts";

const root = join(import.meta.dirname, "..");

// An empty index.html stands in for the built viewer, so the tests pass without building it.
mkdirSync(join(import.meta.dirname, ".fixtures"), { recursive: true });
const viewer = mkdtempSync(join(import.meta.dirname, ".fixtures", "viewer-"));
writeFileSync(join(viewer, "index.html"), "");
after(() => rmSync(viewer, { recursive: true, force: true }));

async function run(...args: string[]): Promise<{ code: number; out: string[]; err: string[] }> {
  const out: string[] = [];
  const err: string[] = [];
  const code = await main(args, {
    cwd: root,
    log: (line) => out.push(line),
    error: (line) => err.push(line),
    viewer,
    typeCheck: () => ({ kind: "ran", passed: true, output: "" }),
  });
  return { code, out, err };
}

async function runWithTsc(...args: string[]): Promise<{ code: number; out: string[]; err: string[] }> {
  const out: string[] = [];
  const err: string[] = [];
  const code = await main(args, { cwd: root, log: (line) => out.push(line), error: (line) => err.push(line) });
  return { code, out, err };
}

test("tazuna writes the usage to stdout and exits with 0 when no argument, --help, or -h is given", async () => {
  for (const args of [[], ["--help"], ["-h"], ["test", "samples/todo/spec", "--help"]]) {
    const { code, out, err } = await run(...args);
    assert.equal(code, 0);
    assert.deepEqual(err, []);
    assert.match(out.join("\n"), /^Usage: tazuna /);
  }
});

test("tazuna writes an error and exits with 2 for an unknown command, a wrong number of arguments, an unknown option, an option without its value, or a missing required option", async () => {
  const cases: [string[], string][] = [
    [["serve", "samples/todo/spec"], "unknown command serve"],
    [["check"], "wrong number of arguments for check"],
    [["verify", "samples/todo/spec"], "wrong number of arguments for verify"],
    [["test", "samples/todo/spec", "--updte"], "unknown option --updte for test"],
    [["check", "samples/todo/spec", "--update"], "unknown option --update for check"],
    [["test", "samples/todo/spec"], "missing option --depth for test"],
    [["view"], "wrong number of arguments for view"],
    [["view", "samples/todo/spec", "--port"], "missing value for --port"],
  ];
  for (const [args, message] of cases) {
    const { code, out, err } = await run(...args);
    assert.equal(code, 2);
    assert.deepEqual(out, []);
    assert.deepEqual(err, [`tazuna: ${message}. Run tazuna --help for usage.`]);
  }
});

test("tazuna writes an error and exits with 2 when the spec folder does not exist, the view port is not an integer from 0 to 65535, or the test depth is not a nonnegative integer", async () => {
  const cases: [string[], string][] = [
    [["check", "samples/nope"], "no such folder samples/nope"],
    [["test", "samples/nope", "--depth", "1"], "no such folder samples/nope"],
    [["verify", "samples/nope", "traces"], "no such folder samples/nope"],
    [["verify", "samples/todo/spec", "nope"], "no such folder nope"],
    [["view", "samples/todo/spec", "--port", "http"], "invalid port http (expected an integer from 0 to 65535)"],
    [["test", "samples/todo/spec", "--depth", "1.5"], "invalid depth 1.5 (expected a non-negative integer)"],
    [["test", "samples/todo/spec", "--depth", "1e0"], "invalid depth 1e0 (expected a non-negative integer)"],
    [["view", "samples/todo/spec", "--port", "0x50"], "invalid port 0x50 (expected an integer from 0 to 65535)"],
  ];
  for (const [args, message] of cases) {
    const { code, out, err } = await run(...args);
    assert.equal(code, 2);
    assert.deepEqual(out, []);
    assert.deepEqual(err, [`tazuna: ${message}.`]);
  }
});

test("view writes an error and exits with 2 when another program uses the port", async () => {
  const other = createServer();
  await new Promise<void>((resolve) => other.listen(0, "localhost", resolve));
  const { port } = other.address() as AddressInfo;
  try {
    const { code, out, err } = await run("view", "samples/todo/spec", "--port", String(port));
    assert.equal(code, 2);
    assert.deepEqual(out, []);
    assert.deepEqual(err, [`tazuna: port ${port} in use.`]);
  } finally {
    other.close();
  }
});

test("check and test write the tsc output to stderr and exit with 1 when tsc reports errors for the nearest tsconfig.json above the spec folder", async () => {
  const project = mkdtempSync(join(import.meta.dirname, ".fixtures", "type-error-"));
  writeFileSync(join(project, "tsconfig.json"), "{}\n");
  writeFileSync(join(project, "count.ts"), 'export const count: number = "one";\n');
  const folder = relative(root, project);
  try {
    const { code, out, err } = await runWithTsc("check", folder);
    assert.equal(code, 1);
    assert.deepEqual(out, []);
    assert.deepEqual(err, [
      `${folder}/count.ts(1,14): error TS2322: Type 'string' is not assignable to type 'number'.`,
    ]);
  } finally {
    rmSync(project, { recursive: true, force: true });
  }
});

test("check and test write an error and exit with 2 when no tsconfig.json is above the spec folder or typescript does not resolve from the spec folder", async () => {
  const outsideRepository = mkdtempSync(join(tmpdir(), "tazuna-"));
  try {
    for (const args of [
      ["check", outsideRepository],
      ["test", outsideRepository, "--depth", "0"],
    ]) {
      const { code, out, err } = await runWithTsc(...args);
      assert.equal(code, 2);
      assert.deepEqual(out, []);
      assert.deepEqual(err, [`tazuna: no tsconfig.json at or above ${outsideRepository}.`]);
    }
    writeFileSync(join(outsideRepository, "tsconfig.json"), "{}\n");
    for (const args of [
      ["check", outsideRepository],
      ["test", outsideRepository, "--depth", "0"],
    ]) {
      const { code, out, err } = await runWithTsc(...args);
      assert.equal(code, 2);
      assert.deepEqual(out, []);
      assert.deepEqual(err, [`tazuna: cannot resolve typescript from ${outsideRepository}.`]);
    }
  } finally {
    rmSync(outsideRepository, { recursive: true, force: true });
  }
});

test("check writes one JSON line per violation to stdout and the count, or that there is no violation, to stderr", async () => {
  const sourcesOf = (folder: string) =>
    readdirSync(join(root, folder), { recursive: true, encoding: "utf8" }).filter((f) => f.endsWith(".ts"));
  const violatingFolder = "test/validation/illegal/commands/emitted-event";
  const violating = await run("check", violatingFolder);
  assert.equal(violating.code, 1);
  assert.deepEqual(
    violating.out.map((line) => (JSON.parse(line) as { readonly kind: string }).kind),
    ["Illegal.foreignEvent"],
  );
  assert.deepEqual(violating.err, [`Checked ${sourcesOf(violatingFolder).length} files. 1 violation.`]);
  const cleanFolder = "test/service/Chart/Always/always";
  const clean = await run("check", cleanFolder);
  assert.equal(clean.code, 0);
  assert.deepEqual(clean.out, []);
  assert.deepEqual(clean.err, [`Checked ${sourcesOf(cleanFolder).length} files. No violations found.`]);
});

test("test writes the same violation lines and count as check and runs no scenario when check reports violations", async () => {
  const folder = "test/load/malformed/times/at";
  const checked = await run("check", folder);
  const tested = await run("test", folder, "--depth", "1");
  assert.equal(tested.code, 1);
  assert.notDeepEqual(checked.out, []);
  assert.deepEqual(tested.out, checked.out);
  assert.deepEqual(tested.err, checked.err);
});

test("Every line of the snapshots under samples conforms to traceLine", () => {
  const samples = join(root, "samples/todo/spec");
  const snapshots = readdirSync(samples, { recursive: true, encoding: "utf8" }).filter((f) => f.endsWith(".jsonl"));
  assert.notEqual(snapshots.length, 0);
  for (const file of snapshots)
    for (const line of readFileSync(join(samples, file), "utf8").trim().split("\n"))
      assert.ok(traceLine.safeParse(JSON.parse(line)).success, `${file}: ${line}`);
});
