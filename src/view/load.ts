import { fork } from "node:child_process";
import { checkSpec, reason, type SpecCheck } from "../check/spec.ts";
import { viewModel } from "./model.ts";
import type { ViewModel } from "./types.ts";

export type Loaded = { readonly model: ViewModel } | { readonly error: string };

function failure(result: Exclude<SpecCheck, { readonly kind: "checked" }>): string {
  switch (result.kind) {
    case "noTsconfig":
      return "no tsconfig.json at or above the spec folder";
    case "noTypescript":
      return "cannot resolve typescript from the spec folder";
    case "unfinished":
      return `tsc did not finish: ${result.reason}`;
    case "typeErrors":
      return result.output;
    case "unloadable":
      return result.reason;
    case "violations":
      return result.violations.map((v) => JSON.stringify(v)).join("\n");
  }
}

if (import.meta.main && process.send !== undefined) {
  const [root = "", path = ""] = process.argv.slice(2);
  const send = (loaded: Loaded) => process.send?.(loaded, () => process.disconnect?.());
  try {
    const result = await checkSpec(root);
    send(result.kind === "checked" ? { model: viewModel(result.spec, path) } : { error: failure(result) });
  } catch (error) {
    send({ error: reason(error) });
  }
}

/**
 * Checks the spec and loads its view model in a forked process. Node caches imported modules and never reloads an
 * edited spec file in the same process, so each load forks.
 */
export function loadViewModel(root: string, path: string): Promise<Loaded> {
  return new Promise((resolve) => {
    let loaded: Loaded | undefined;
    fork(import.meta.filename, [root, path], { stdio: ["ignore", "inherit", "inherit", "ipc"] })
      .on("message", (message) => {
        loaded = message as Loaded;
      })
      .on("exit", (code) => resolve(loaded ?? { error: `the spec loader exited with code ${code}` }));
  });
}
