import { fork } from "node:child_process";
import { checkSpec, failureText } from "../check/spec.ts";
import { typeCheck } from "../check/typeCheck.ts";
import { viewModel } from "./model.ts";
import type { ViewModel } from "./types.ts";

export type Loaded = { readonly model: ViewModel } | { readonly error: string };

if (import.meta.main && process.send !== undefined) {
  const [root = "", path = "", cwd = ""] = process.argv.slice(2);
  const result = await checkSpec(root, typeCheck(root, cwd));
  const loaded: Loaded =
    result.kind === "checked" ? { model: viewModel(result.spec, path) } : { error: failureText(result, path) };
  process.send?.(loaded, () => process.disconnect?.());
}

/**
 * Checks the spec as the CLI does, with tsc run in `cwd`, and loads its view model in a forked process. Node caches
 * imported modules and never reloads an edited spec file in the same process, so each load forks.
 */
export function loadViewModel(root: string, path: string, cwd: string): Promise<Loaded> {
  return new Promise((resolve) => {
    let loaded: Loaded | undefined;
    fork(import.meta.filename, [root, path, cwd], { stdio: ["ignore", "inherit", "inherit", "ipc"] })
      .on("message", (message) => {
        loaded = message as Loaded;
      })
      .on("exit", (code) => resolve(loaded ?? { error: `the spec loader exited with code ${code}` }));
  });
}
