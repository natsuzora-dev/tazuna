import { existsSync, readdirSync } from "node:fs";
import { basename, join, relative } from "node:path";
import { check } from "../src/cli/check.ts";
import type { ProblemError } from "../src/data/violation.ts";
import { loadSpec, type Spec } from "../src/load/load.ts";

export const semanticsRoot = join(import.meta.dirname, "semantics");
export const runRoot = join(import.meta.dirname, "run");
export const leanRoot = join(import.meta.dirname, "../lean/Tazuna");

export const folders = (dir: string): string[] =>
  existsSync(dir)
    ? readdirSync(dir, { withFileTypes: true })
        .filter((d) => d.isDirectory())
        .map((d) => join(dir, d.name))
        .sort()
    : [];

/**
 * The number of inputs appended to each scenario when the examples run under test and the Lean oracle. 2, since 3
 * makes npm test and npm run lean:check several times slower.
 */
export const depth = 2;

export const isServiceFolder = (dir: string): boolean => readdirSync(dir).some((name) => name.endsWith(".ts"));

/**
 * Loads the spec of the example `root` and throws when check reports a violation in it, because tazuna test runs only a
 * spec without one.
 */
export async function loadRoot(root: string): Promise<Spec> {
  const spec = await loadSpec(root);
  const found = check(spec);
  const name = relative(join(import.meta.dirname, ".."), root);
  if (found.length > 0) throw new Error(`${name} is no root: check reports ${found.map((p) => p.kind).join(", ")}`);
  return spec;
}

/** Returns the examples test/<folder>/<group>/<target>/<example> of `group`, or of every group without it. */
export const groupExamples = (folder: string, group?: string): string[] =>
  (group === undefined
    ? folders(join(import.meta.dirname, folder))
    : [join(import.meta.dirname, folder, group)]
  ).flatMap((f) => folders(f).flatMap(folders));

/** Returns the paths of the Lean modules relative to Tazuna/<folder>, such as Chart/Always in Semantics. */
export const leanModulePaths = (folder: string): string[] =>
  readdirSync(join(leanRoot, folder), { recursive: true, encoding: "utf8" })
    .filter((file) => file.endsWith(".lean"))
    .map((file) => file.slice(0, -".lean".length))
    .sort();

/** Returns the folder under lean/Tazuna of the Lean file that defines `group`, such as Semantics for fault. */
export const leanFolderOf = (group: string): string => {
  const file = `${group.charAt(0).toUpperCase()}${group.slice(1)}.lean`;
  const found = readdirSync(leanRoot).filter((folder) => existsSync(join(leanRoot, folder, file)));
  if (found.length !== 1) throw new Error(`no single folder under lean/Tazuna has ${file}`);
  return found[0] as string;
};

/** Returns the folders directly under <root>/<path of a Lean module under Tazuna/<folder>>. */
const atLeanPaths = (root: string, folder: string): string[] =>
  leanModulePaths(folder).flatMap((path) => folders(join(root, path)));

/** Returns the semantics subjects: the folders directly under test/semantics/<Lean Semantics path>. */
export const semanticsSubjects = (): string[] => atLeanPaths(semanticsRoot, "Semantics");

/** Returns the examples test/run/<group>/<path of a Lean module in the group's Lean folder>/<example>. */
export const runGroupExamples = (group: string): string[] => atLeanPaths(join(runRoot, group), leanFolderOf(group));

/** Returns the roots that run.test compares with their expected.jsonl and that run.diff and step.test run. */
export const runExamples = (): string[] => [
  ...semanticsSubjects(),
  ...folders(runRoot).flatMap((folder) => runGroupExamples(basename(folder))),
];

/**
 * Replaces the stack of the error with a placeholder, because a stack changes with any edit of src and with the caller
 * of the run.
 */
export function maskedStack<T extends { readonly error?: ProblemError }>(value: T): T {
  const { error } = value;
  return error !== undefined && "stack" in error ? { ...value, error: { ...error, stack: "<stack>" } } : value;
}
