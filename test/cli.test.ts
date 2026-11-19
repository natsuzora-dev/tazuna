import assert from "node:assert/strict";
import { cpSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { createServer } from "node:http";
import type { AddressInfo } from "node:net";
import { tmpdir } from "node:os";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { main } from "../src/cli/main.ts";
import { traceLine } from "../src/data/trace.generated.ts";
import { typeChecked } from "./examples.ts";

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
    typeCheck: () => typeChecked,
  });
  return { code, out, err };
}

async function runWithTsc(...args: string[]): Promise<{ code: number; out: string[]; err: string[] }> {
  const out: string[] = [];
  const err: string[] = [];
  const code = await main(args, { cwd: root, log: (line) => out.push(line), error: (line) => err.push(line), viewer });
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
    [["constructor", "samples/todo/spec"], "unknown command constructor"],
    [["__proto__", "samples/todo/spec"], "unknown command __proto__"],
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

test("check, test, verify, and view write the tsc output to stderr and exit with 1 when tsc reports errors for the nearest tsconfig.json above the spec folder", async () => {
  const project = mkdtempSync(join(import.meta.dirname, ".fixtures", "type-error-"));
  writeFileSync(join(project, "tsconfig.json"), "{}\n");
  writeFileSync(join(project, "count.ts"), 'export const count: number = "one";\n');
  const folder = relative(root, project);
  try {
    for (const args of [
      ["check", folder],
      ["test", folder, "--depth", "0"],
      ["verify", folder, folder],
      ["view", folder],
    ]) {
      const { code, out, err } = await runWithTsc(...args);
      assert.equal(code, 1);
      assert.deepEqual(out, []);
      assert.deepEqual(err, [
        `${folder}/count.ts(1,14): error TS2322: Type 'string' is not assignable to type 'number'.`,
      ]);
    }
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

test("check, test, and verify write one line with the error and its place and exit with 2 when a spec file throws when imported", async () => {
  const project = mkdtempSync(join(import.meta.dirname, ".fixtures", "import-error-"));
  writeFileSync(join(project, "broken.ts"), 'throw new Error("no spec here");\n');
  const folder = relative(root, project);
  try {
    for (const args of [
      ["check", folder],
      ["test", folder, "--depth", "0"],
      ["verify", folder, folder],
    ]) {
      const { code, out, err } = await run(...args);
      assert.equal(code, 2);
      assert.deepEqual(out, []);
      assert.equal(err.length, 1);
      assert.match(
        err[0] ?? "",
        new RegExp(`^tazuna: cannot load ${folder}: Error: no spec here at \\S*broken\\.ts:1:7\\.$`),
      );
    }
  } finally {
    rmSync(project, { recursive: true, force: true });
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

test("test writes how many scenarios it ran out of all and the depth to stderr, and with --only runs only the named scenarios and leaves the snapshots of the others unreported and unremoved", async () => {
  const project = mkdtempSync(join(import.meta.dirname, ".fixtures", "only-"));
  cpSync(join(import.meta.dirname, "verify/uncomparable/snapshot/unpaired"), project, { recursive: true });
  const folder = relative(root, project);
  const snapshots = join(project, "todo/__snapshots__");
  const entries = readdirSync(snapshots).toSorted();
  try {
    const all = await run("test", folder, "--depth", "0");
    assert.equal(all.code, 1);
    assert.deepEqual(all.err, ["2/2 scenarios, depth 0: 4 violations"]);
    const one = await run("test", folder, "--depth", "0", "--only", "todo/addOne", "--update");
    assert.equal(one.code, 0);
    assert.deepEqual(one.out, []);
    assert.deepEqual(one.err.at(-1), "1/2 scenarios (--only), depth 0: no violations");
    assert.deepEqual(readdirSync(snapshots).toSorted(), entries);
    const both = await run(
      "test",
      folder,
      "--depth",
      "1",
      "--only",
      "todo/addOneUnsnapshotted",
      "--only",
      "todo/addOne",
    );
    assert.deepEqual(
      both.out.map((line) => (JSON.parse(line) as { readonly kind: string }).kind),
      ["Uncomparable.missingSnapshot"],
    );
    assert.deepEqual(both.err, ["2/2 scenarios (--only), depth 1: 1 violation"]);
  } finally {
    rmSync(project, { recursive: true, force: true });
  }
});

test("test writes an error and exits with 2 when --only names no scenario of the spec or comes with --coverage", async () => {
  const folder = "test/verify/uncomparable/snapshot/unpaired";
  const cases: [string[], string][] = [
    [["--only", "todo/addOn"], "unknown scenario todo/addOn"],
    [["--only", "addOne"], "unknown scenario addOne"],
    [["--only", "todo/addOne", "--coverage"], "--coverage cannot be given with --only"],
  ];
  for (const [args, message] of cases) {
    const { code, out, err } = await run("test", folder, "--depth", "0", ...args);
    assert.equal(code, 2);
    assert.deepEqual(out, []);
    assert.deepEqual(err, [`tazuna: ${message}.`]);
  }
});

test("explain writes the markdown of a violation kind: its meaning, its group, who reports it, the side at fault, and an example", async () => {
  const { code, out, err } = await run("explain", "Fault.failedEnsures");
  assert.equal(code, 0);
  assert.deepEqual(err, []);
  const markdown = out.join("\n");
  assert.match(
    markdown,
    /^# Fault\.failedEnsures\n\nThe answer of the command or query, or the output of the screen, fails its ensures `condition`\./,
  );
  assert.match(markdown, /\n- Reported by: `test`\n- Side at fault: The spec\.\n/);
  assert.match(
    markdown,
    /\n## Example\n\n`[^`]+\.ts`, lines? \d+[^\n]*:\n\n```ts\n[\s\S]*\nThe violation:\n\n```json\n\{"kind":"Fault\.failedEnsures"/,
  );
});

test("explain writes an error and exits with 2 for a name that is no violation kind", async () => {
  for (const kind of ["Fault.nope", "Fault", "fault.failedEnsures", "constructor"]) {
    const { code, out, err } = await run("explain", kind);
    assert.equal(code, 2);
    assert.deepEqual(out, []);
    assert.deepEqual(err, [`tazuna: unknown kind ${kind}.`]);
  }
});

test("test, verify, and view write the same violation lines and count as check and do nothing else when check reports violations", async () => {
  const folder = "test/load/malformed/times/at";
  const checked = await run("check", folder);
  assert.notDeepEqual(checked.out, []);
  for (const args of [
    ["test", folder, "--depth", "1"],
    ["verify", folder, folder],
    ["view", folder],
  ]) {
    const { code, out, err } = await run(...args);
    assert.equal(code, 1);
    assert.deepEqual(out, checked.out);
    assert.deepEqual(err, checked.err);
  }
});

test("check reports each spec file that the program of the nearest tsconfig.json leaves out", async () => {
  const project = mkdtempSync(join(import.meta.dirname, ".fixtures", "unlisted-"));
  writeFileSync(join(project, "tsconfig.json"), '{ "extends": "../../../tsconfig.base.json", "include": ["src"] }\n');
  mkdirSync(join(project, "src"));
  writeFileSync(join(project, "src/app.ts"), "export {};\n");
  cpSync(join(import.meta.dirname, "service/Chart/Config/history/player"), join(project, "spec/player"), {
    recursive: true,
  });
  const folder = relative(root, join(project, "spec"));
  try {
    const { code, out } = await runWithTsc("check", folder);
    assert.equal(code, 1);
    assert.deepEqual(
      out.map((line) => JSON.parse(line)),
      ["contract.ts", "machines.ts", "player.ts", "scenarios.ts"].map((file) => ({
        kind: "Malformed.unlistedFile",
        definition: null,
        data: { tsconfig: "../tsconfig.json" },
        location: { file: `${folder}/player/${file}`, line: 1 },
      })),
    );
  } finally {
    rmSync(project, { recursive: true, force: true });
  }
});

test("check skips node_modules folders and .d.ts files, and walks a symlinked folder once", async () => {
  const project = mkdtempSync(join(import.meta.dirname, ".fixtures", "walk-"));
  cpSync(join(import.meta.dirname, "service/Chart/Config/history/player"), join(project, "player"), {
    recursive: true,
  });
  mkdirSync(join(project, "node_modules/helper"), { recursive: true });
  writeFileSync(join(project, "node_modules/helper/index.ts"), 'throw new Error("imported node_modules");\n');
  writeFileSync(join(project, "player/ambient.d.ts"), 'throw new Error("imported a declaration file");\n');
  symlinkSync("..", join(project, "player/up"));
  const folder = relative(root, project);
  try {
    const { code, out, err } = await run("check", folder);
    assert.equal(code, 0);
    assert.deepEqual(out, []);
    assert.deepEqual(err, ["Checked 4 files. No violations found."]);
  } finally {
    rmSync(project, { recursive: true, force: true });
  }
});

test("Every line of the snapshots under samples conforms to traceLine", () => {
  const samples = join(root, "samples/todo/spec");
  const snapshots = readdirSync(samples, { recursive: true, encoding: "utf8" }).filter((f) => f.endsWith(".jsonl"));
  assert.notEqual(snapshots.length, 0);
  for (const file of snapshots)
    for (const line of readFileSync(join(samples, file), "utf8").trim().split("\n"))
      assert.ok(traceLine.safeParse(JSON.parse(line)).success, `${file}: ${line}`);
});
