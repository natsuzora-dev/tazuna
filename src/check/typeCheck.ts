import { spawnSync } from "node:child_process";
import { existsSync, realpathSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import type * as Api from "typescript/unstable/sync";

/**
 * The result of a type check. `output` is what tsc wrote to stdout, then to stderr; `includes` tells whether the
 * program of the tsconfig, as the TypeScript API reads it, has the file at an absolute path.
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
 * that `specRoot` resolves, in `cwd`.
 */
export function typeCheck(specRoot: string, cwd: string): TypeCheck {
  const tsconfig = nearestTsconfig(specRoot);
  if (tsconfig === undefined) return { kind: "noTsconfig" };
  // The trailing slash makes createRequire resolve from specRoot, not its parent.
  const resolveTypescript = createRequire(join(specRoot, "/"));
  let typescript: string;
  try {
    typescript = resolveTypescript.resolve("typescript/package.json");
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
  if (result.status !== 0) return { kind: "typeErrors", output: result.stdout + result.stderr };
  const { API }: typeof Api = resolveTypescript("typescript/unstable/sync");
  const api = new API({ cwd });
  try {
    const project = api.updateSnapshot({ openProjects: [tsconfig] }).getProject(tsconfig);
    if (project === undefined) return { kind: "unfinished", reason: `the TypeScript API did not open ${tsconfig}` };
    const files = new Set(project.program.getSourceFileNames());
    return { kind: "passed", tsconfig, includes: (file) => files.has(file) || files.has(realpathSync(file)) };
  } finally {
    api.close();
  }
}
