import { spawnSync } from "node:child_process";
import { existsSync, realpathSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";

/**
 * The result of a type check. `output` is what tsc wrote to stdout, then to stderr; `includes` tells whether the
 * program of the tsconfig, as `tsc --listFilesOnly` lists it, has the file at an absolute path.
 */
export type TypeCheck =
  | { readonly kind: "noTsconfig" }
  | { readonly kind: "noTypescript" }
  | { readonly kind: "unfinished"; readonly reason: string }
  | { readonly kind: "typeErrors"; readonly output: string }
  | { readonly kind: "passed"; readonly tsconfig: string; readonly includes: (file: string) => boolean };

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
    spawnSync(process.execPath, [tsc, flag, "-p", tsconfig], { cwd, encoding: "utf8", maxBuffer: Infinity });
  const unfinished = (result: ReturnType<typeof run>): TypeCheck | undefined => {
    if (result.error !== undefined) return { kind: "unfinished", reason: result.error.message };
    if (result.signal !== null) return { kind: "unfinished", reason: `terminated by ${result.signal}` };
    return undefined;
  };
  const checked = run("--noEmit");
  const failed = unfinished(checked);
  if (failed !== undefined) return failed;
  if (checked.status !== 0) return { kind: "typeErrors", output: checked.stdout + checked.stderr };
  // --listFilesOnly writes each file of the program as a line of its own, and nothing else.
  const listed = run("--listFilesOnly");
  const notListed = unfinished(listed);
  if (notListed !== undefined) return notListed;
  if (listed.status !== 0) return { kind: "unfinished", reason: listed.stdout + listed.stderr };
  const files = new Set(listed.stdout.split(/\r?\n/).filter((line) => line !== ""));
  return { kind: "passed", tsconfig, includes: (file) => files.has(file) || files.has(realpathSync(file)) };
}
