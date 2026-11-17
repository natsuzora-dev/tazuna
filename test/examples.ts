import { existsSync, readdirSync } from "node:fs";
import { basename, join, relative } from "node:path";
import { type CheckedSpec, checkSpecWith, failureText } from "../src/check/spec.ts";
import type { TypeCheck } from "../src/check/typeCheck.ts";
import type { ViolationError } from "../src/data/violation.ts";

export const serviceRoot = join(import.meta.dirname, "service");
export const runRoot = join(import.meta.dirname, "run");
export const simRoot = join(import.meta.dirname, "sim");
export const leanRoot = join(import.meta.dirname, "../lean/Tazuna");

export const folders = (dir: string): string[] =>
  existsSync(dir)
    ? readdirSync(dir, { withFileTypes: true })
        .filter((d) => d.isDirectory())
        .map((d) => join(dir, d.name))
        .sort()
    : [];

/**
 * The most moves on a path after each scenario when the examples run under test and the Lean oracle. 2, since 3
 * makes npm test and npm run lean:check several times slower.
 */
export const depth = 2;

export const isServiceFolder = (dir: string): boolean => readdirSync(dir).some((name) => name.endsWith(".ts"));

/** A passed type check whose program includes every file, which the examples take in place of running tsc. */
export const typeChecked: TypeCheck = { kind: "passed", tsconfig: "", includes: () => true };

/** Checks the spec of the example `root` with typeChecked, and throws unless it is checked. */
export async function checkedRoot(root: string): Promise<CheckedSpec> {
  const result = await checkSpecWith(root, typeChecked);
  if (result.kind === "checked") return result.spec;
  const name = relative(join(import.meta.dirname, ".."), root);
  throw new Error(`${name} is not checked:\n${failureText(result, name)}`);
}

/** Returns the examples test/<folder>/<group>/<target>/<example> of `group`, or of every group without it. */
export const groupExamples = (folder: string, group?: string): string[] =>
  (group === undefined
    ? folders(join(import.meta.dirname, folder))
    : [join(import.meta.dirname, folder, group)]
  ).flatMap((f) => folders(f).flatMap(folders));

/** Returns the paths of the Lean modules relative to Tazuna/<folder>, such as Chart/Always in Service. */
export const leanModulePaths = (folder: string): string[] =>
  readdirSync(join(leanRoot, folder), { recursive: true, encoding: "utf8" })
    .filter((file) => file.endsWith(".lean"))
    .map((file) => file.slice(0, -".lean".length))
    .sort();

/** Returns the paths relative to Tazuna of the Lean modules outside Thm, such as Service/Chart/Always. */
export const leanDefinitionPaths = (): string[] => leanModulePaths("").filter((path) => !path.startsWith("Thm/"));

const atPaths = (root: string, paths: readonly string[]): string[] =>
  paths.flatMap((path) => folders(join(root, path)));

/** Returns the subjects: the folders directly under test/service/<Lean Service path>. */
export const subjects = (): string[] => atPaths(serviceRoot, leanModulePaths("Service"));

/** Returns the examples test/run/<group>/<path of a Lean module under Tazuna, outside Thm>/<example>. */
export const runGroupExamples = (group: string): string[] => atPaths(join(runRoot, group), leanDefinitionPaths());

/** Returns the roots that run.test compares with their expected.jsonl and that run.diff and step.test run. */
export const runExamples = (): string[] => [
  ...subjects(),
  ...folders(runRoot).flatMap((folder) => runGroupExamples(basename(folder))),
];

/**
 * Replaces the stack of the error with a placeholder, because a stack changes with any edit of src and with the caller
 * of the run.
 */
export function maskedStack<T extends { readonly error?: ViolationError }>(value: T): T {
  const { error } = value;
  return error !== undefined && "stack" in error ? { ...value, error: { ...error, stack: "<stack>" } } : value;
}

export const scenarioSuffix = ".scenario.json";
export const outcomeSuffix = ".expected.json";

/** Returns the examples test/sim/<Lean Sim module path>/<example>/, each with the names of its scenario files. */
export const simExamples = (): { readonly root: string; readonly scenarios: readonly string[] }[] =>
  atPaths(simRoot, leanModulePaths("Sim")).map((root) => ({
    root,
    scenarios: readdirSync(root)
      .filter((name) => name.endsWith(scenarioSuffix))
      .map((name) => name.slice(0, -scenarioSuffix.length))
      .sort(),
  }));
