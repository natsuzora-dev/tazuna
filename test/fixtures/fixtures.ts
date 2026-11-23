import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";
import { after } from "node:test";
import { explanations, violationOfLine } from "../../scripts/explain.ts";
import { type ConvertedSpec, checkSpecWith, failureText } from "../../src/check/spec.ts";
import type { TypeCheck } from "../../src/check/typeCheck.ts";
import { main } from "../../src/cli/main.ts";
import type { Outcome, Verdict } from "../../src/cli/protocol.generated.ts";
import { Converter } from "../../src/convert/program.ts";
import { groups } from "../../src/data/groups.ts";
import type { Group, ViolationError } from "../../src/data/violation.ts";
import { loadSpec, type Spec } from "../../src/load/load.ts";

/**
 * The fixtures: test/fixtures/<command>/<kind>/<case>/, each case the inputs of one run of `tazuna <command>` in the
 * case's folder and the lines it writes, in expected.jsonl. <kind> is what every line of expected.jsonl reports: the
 * group of each violation's kind, prove's verdict, or generate's outcome. A test case that reports no violation is
 * under noViolations.
 */
export const fixturesRoot = import.meta.dirname;

export const expected = "expected.jsonl";

export const noViolations = "noViolations";

/** The kinds of each command: the folder names that test/fixtures/<command> may hold. */
export const kinds = {
  check: groupsReportedBy("check"),
  test: [...groupsReportedBy("test"), noViolations],
  verify: [...groupsReportedBy("verify", "verify --coverage")],
  prove: ["proved", "counterexample", "undecided"] satisfies Verdict["kind"][],
  generate: ["reached", "notReached", "unreachable", "notEncodable"] satisfies Outcome["kind"][],
} as const;

export type Command = keyof typeof kinds;

function groupsReportedBy(...commands: readonly string[]): Group[] {
  return (Object.keys(groups) as Group[]).filter((g) => groups[g].reportedBy.some((c: string) => commands.includes(c)));
}

export const folders = (dir: string): string[] =>
  existsSync(dir)
    ? readdirSync(dir, { withFileTypes: true })
        .filter((d) => d.isDirectory())
        .map((d) => join(dir, d.name))
        .sort()
    : [];

/** The cases of `command` under the kind `kind`. */
export const fixtures = (command: Command, kind: string): string[] => folders(join(fixturesRoot, command, kind));

/** Every case of every command and kind. */
export const allFixtures = (): string[] =>
  (Object.keys(kinds) as Command[]).flatMap((command) => kinds[command].flatMap((kind) => fixtures(command, kind)));

/** The case `name` of `command` under `kind`. */
export const fixture = (command: Command, kind: string, name: string): string =>
  join(fixturesRoot, command, kind, name);

export const isServiceFolder = (dir: string): boolean => readdirSync(dir).some((name) => name.endsWith(".ts"));

/** A passed type check whose program includes every file, which the fixtures take in place of running tsc. */
export const typeChecked: TypeCheck = { kind: "passed", tsconfig: "", includes: () => true };

/** Checks the spec of the fixture `root` with typeChecked, and throws unless it is checked. */
export async function checkedRoot(root: string): Promise<ConvertedSpec> {
  const result = await checkSpecWith(root, typeChecked);
  if (result.kind === "checked") return result.spec;
  const name = relative(join(import.meta.dirname, "../.."), root);
  throw new Error(`${name} is not checked:\n${failureText(result, name)}`);
}

/** Loads the spec of the fixture `root`, and throws when loading finds a Malformed violation. */
export async function loadedSpec(root: string): Promise<Spec> {
  const loaded = await loadSpec(root);
  if (loaded.kind === "malformed")
    throw new Error(`${root}: ${loaded.malformed.map((f) => f.violation.kind).join(", ")}`);
  return loaded.spec;
}

/**
 * Replaces the stack of the error with a placeholder, because a stack changes with any edit of src and with the caller
 * of the run.
 */
export function maskedStack<T extends { readonly error?: ViolationError }>(value: T): T {
  const { error } = value;
  return error !== undefined && "stack" in error ? { ...value, error: { ...error, stack: "<stack>" } } : value;
}

export const expectedOf = (root: string): string[] =>
  readFileSync(join(root, expected), "utf8")
    .split("\n")
    .filter((line) => line !== "");

export const kindOfLine = (line: string) => (violationOfLine(line) as { readonly kind: string }).kind;

let shared: Converter | undefined;
after(() => shared?.close());

/** The converter that the runs of one test file share, since each converter starts tsgo. */
const converter = (): Converter => {
  shared ??= new Converter();
  return shared;
};

/** The summary line that each command writes to stderr, its only line there. */
const summaries = {
  violations: /^[^:\n]+: (?:no violations|\d+ violations?)$/,
  prove: /^\d+ propert(y|ies): \d+ proved, \d+ counterexamples?, \d+ undecided$/,
  generate: /^\d+ targets?: \d+ reached, \d+ not reached, \d+ unreachable, \d+ not encodable; \d+ inputs? written$/,
};

/** The lines that `tazuna <args>` writes to stdout in the folder `root`, and its exit code. */
export async function run(
  root: string,
  args: readonly string[],
): Promise<{ readonly lines: readonly string[]; readonly code: number }> {
  const [name = ""] = args;
  const summary = name === "prove" || name === "generate" ? summaries[name] : summaries.violations;
  const lines: string[] = [];
  const code = await main(args, {
    cwd: root,
    log: (line) => lines.push(line),
    error: (line) => {
      if (!summary.test(line)) throw new Error(`tazuna ${args.join(" ")} wrote ${line} to stderr`);
    },
    ...(existsSync(join(root, "tsconfig.json")) ? {} : { typeCheck: () => typeChecked, converter: converter() }),
  });
  return { lines, code };
}

let explainFile: string | undefined;

/**
 * An explain.json built from the fixtures, which this process deletes on exit: a hook of node:test would run after the
 * test that first asks for it.
 */
export function builtExplanations(): string {
  if (explainFile !== undefined) return explainFile;
  mkdirSync(join(fixturesRoot, "../.fixtures"), { recursive: true });
  const dir = mkdtempSync(join(fixturesRoot, "../.fixtures", "explain-"));
  process.once("exit", () => rmSync(dir, { recursive: true, force: true }));
  explainFile = join(dir, "explain.json");
  writeFileSync(explainFile, JSON.stringify(explanations()));
  return explainFile;
}
