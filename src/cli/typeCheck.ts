import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";

/** The result of a type check. `output` is what tsc wrote to stdout, then to stderr. */
export type TypeCheck =
  | { readonly kind: "noTsconfig" }
  | { readonly kind: "noTypescript" }
  | { readonly kind: "unfinished"; readonly reason: string }
  | { readonly kind: "ran"; readonly passed: boolean; readonly output: string };

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
  const result = spawnSync(process.execPath, [tsc, "--noEmit", "-p", tsconfig], {
    cwd,
    encoding: "utf8",
    maxBuffer: Infinity,
  });
  if (result.error !== undefined) return { kind: "unfinished", reason: result.error.message };
  if (result.signal !== null) return { kind: "unfinished", reason: `terminated by ${result.signal}` };
  return { kind: "ran", passed: result.status === 0, output: result.stdout + result.stderr };
}
