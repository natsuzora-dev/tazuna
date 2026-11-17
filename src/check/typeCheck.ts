import { spawnSync } from "node:child_process";
import { existsSync, realpathSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, isAbsolute, join } from "node:path";

/**
 * The result of a type check. `output` is what tsc wrote to stdout, then to stderr, without the file list;
 * `includes` tells whether tsc's program has the file at an absolute path.
 */
export type TypeCheck =
  | { readonly kind: "noTsconfig" }
  | { readonly kind: "noTypescript" }
  | { readonly kind: "unfinished"; readonly reason: string }
  | {
      readonly kind: "ran";
      readonly passed: boolean;
      readonly output: string;
      readonly tsconfig: string;
      readonly includes: (file: string) => boolean;
    };

function nearestTsconfig(folder: string): string | undefined {
  const tsconfig = join(folder, "tsconfig.json");
  if (existsSync(tsconfig)) return tsconfig;
  const parent = dirname(folder);
  return parent === folder ? undefined : nearestTsconfig(parent);
}

/**
 * Runs `tsc --noEmit -p` on the nearest tsconfig.json at or above `specRoot`, with the tsc of the typescript package
 * that `specRoot` resolves, in `cwd`.
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
  const result = spawnSync(process.execPath, [tsc, "--noEmit", "--listFiles", "-p", tsconfig], {
    cwd,
    encoding: "utf8",
    maxBuffer: Infinity,
  });
  if (result.error !== undefined) return { kind: "unfinished", reason: result.error.message };
  if (result.signal !== null) return { kind: "unfinished", reason: `terminated by ${result.signal}` };
  // --listFiles writes each file of the program as a line of its own: an absolute path that exists.
  const lines = (result.stdout + result.stderr).split(/\r?\n/);
  const isListed = (line: string) => isAbsolute(line) && existsSync(line);
  const files = new Set(lines.filter(isListed));
  return {
    kind: "ran",
    passed: result.status === 0,
    output: lines.filter((line) => !isListed(line)).join("\n"),
    tsconfig,
    includes: (file) => files.has(file) || files.has(realpathSync(file)),
  };
}
