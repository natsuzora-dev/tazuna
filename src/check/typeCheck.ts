import { spawnSync } from "node:child_process";
import { existsSync, realpathSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";

/** An error that tsc reports, at an absolute path and line, or at none for an error of the whole program. */
export interface TscError {
  readonly at?: { readonly file: string; readonly line: number; readonly column: number };
  /** The TypeScript error code, such as TS2322. */
  readonly code: string;
  /** The message, with each further line of its chain on a line of its own. */
  readonly message: string;
}

/**
 * The result of a type check. `includes` tells whether the program of the tsconfig, as `tsc --listFilesOnly` lists it,
 * has the file at an absolute path.
 */
export type TypeCheck =
  | { readonly kind: "noTsconfig" }
  | { readonly kind: "noTypescript" }
  | { readonly kind: "unfinished"; readonly reason: string }
  | { readonly kind: "typeErrors"; readonly tsconfig: string; readonly errors: readonly TscError[] }
  | { readonly kind: "passed"; readonly tsconfig: string; readonly includes: (file: string) => boolean };

/**
 * The errors of tsc's `--pretty false` output, whose paths are relative to `cwd`: `<file>(<line>,<column>): error
 * <code>: <message>` or `error <code>: <message>`, each further line of a message indented. Undefined when a line has
 * neither form.
 */
function tscErrors(output: string, cwd: string): TscError[] | undefined {
  const errors: TscError[] = [];
  for (const line of output.split(/\r?\n/)) {
    if (line === "") continue;
    const last = errors.at(-1);
    if (/^\s/.test(line) && last !== undefined) {
      errors[errors.length - 1] = { ...last, message: `${last.message}\n${line.trim()}` };
      continue;
    }
    const placed = /^(.+)\((\d+),(\d+)\): error (TS\d+): (.*)$/.exec(line);
    if (placed !== null) {
      const [, file = "", row = "", column = "", code = "", message = ""] = placed;
      errors.push({ at: { file: resolve(cwd, file), line: Number(row), column: Number(column) }, code, message });
      continue;
    }
    const global = /^error (TS\d+): (.*)$/.exec(line);
    if (global === null) return undefined;
    const [, code = "", message = ""] = global;
    errors.push({ code, message });
  }
  return errors;
}

function nearestTsconfig(folder: string): string | undefined {
  const tsconfig = join(folder, "tsconfig.json");
  if (existsSync(tsconfig)) return tsconfig;
  const parent = dirname(folder);
  return parent === folder ? undefined : nearestTsconfig(parent);
}

/**
 * Runs `tsc --noEmit -p` on the nearest tsconfig.json at or above `specRoot`, with the tsc of the typescript package
 * that `specRoot` resolves, in `cwd`, and on success lists the program's files with `tsc --listFilesOnly -p`.
 */
export function typeCheck(specRoot: string, cwd: string): TypeCheck {
  const tsconfig = nearestTsconfig(specRoot);
  if (tsconfig === undefined) return { kind: "noTsconfig" };
  let typescript: string;
  try {
    // The trailing slash makes createRequire resolve from specRoot, not its parent.
    typescript = createRequire(join(specRoot, "/")).resolve("typescript/package.json");
  } catch {
    return { kind: "noTypescript" };
  }
  const tsc = join(dirname(typescript), "bin", "tsc");
  const run = (flag: string) =>
    spawnSync(process.execPath, [tsc, flag, "--pretty", "false", "-p", tsconfig], {
      cwd,
      encoding: "utf8",
      maxBuffer: Infinity,
    });
  const unfinished = (result: ReturnType<typeof run>): TypeCheck | undefined => {
    if (result.error !== undefined) return { kind: "unfinished", reason: result.error.message };
    if (result.signal !== null) return { kind: "unfinished", reason: `terminated by ${result.signal}` };
    return undefined;
  };
  const checked = run("--noEmit");
  const failed = unfinished(checked);
  if (failed !== undefined) return failed;
  if (checked.status !== 0) {
    const output = checked.stdout + checked.stderr;
    const errors = tscErrors(output, cwd);
    return errors === undefined || errors.length === 0
      ? { kind: "unfinished", reason: output }
      : { kind: "typeErrors", tsconfig, errors };
  }
  // --listFilesOnly writes each file of the program as a line of its own, and nothing else.
  const listed = run("--listFilesOnly");
  const notListed = unfinished(listed);
  if (notListed !== undefined) return notListed;
  if (listed.status !== 0) return { kind: "unfinished", reason: listed.stdout + listed.stderr };
  const files = new Set(listed.stdout.split(/\r?\n/).filter((line) => line !== ""));
  return { kind: "passed", tsconfig, includes: (file) => files.has(file) || files.has(realpathSync(file)) };
}
