import { fork } from "node:child_process";
import { loadSpec } from "../load/load.ts";
import { viewModel } from "./model.ts";
import type { ViewModel } from "./types.ts";

export type Loaded = { readonly model: ViewModel } | { readonly error: string };

/** Returns the header lines of Node's error and the first stack frame outside node: internals. */
export function reason(error: unknown): string {
  if (!(error instanceof Error)) return String(error);
  const lines = (error.stack ?? error.message).split("\n");
  const frames = lines.findIndex((line) => line.startsWith("    at "));
  if (frames === -1) return lines.join("\n");
  const own = lines.slice(frames).find((line) => !line.includes("(node:") && !line.includes(" node:"));
  return [...lines.slice(0, frames), ...(own === undefined ? [] : [own])].join("\n");
}

if (import.meta.main && process.send !== undefined) {
  const [root = "", path = ""] = process.argv.slice(2);
  const send = (loaded: Loaded) => process.send?.(loaded, () => process.disconnect?.());
  try {
    send({ model: viewModel(await loadSpec(root), path) });
  } catch (error) {
    send({ error: reason(error) });
  }
}

/**
 * Loads the view model in a forked process. Node caches imported modules and never reloads an edited spec file in the
 * same process, so each load forks.
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
