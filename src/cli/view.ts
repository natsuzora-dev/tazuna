import { existsSync } from "node:fs";
import { join } from "node:path";
import type { CheckedSpec } from "../check/spec.ts";
import { viewModel } from "../view/model.ts";
import { serveViewer } from "../view/server.ts";

export const viewerFolder = join(import.meta.dirname, "../../dist/viewer");

export const isViewerBuilt = (folder: string): boolean => existsSync(join(folder, "index.html"));

/** Serves the viewer of the spec named `path` on `port`; undefined when the port is in use. */
export async function viewSpec(spec: CheckedSpec, path: string, port: number, folder: string) {
  const loaded = { model: viewModel(spec, path) };
  return serveViewer({ root: spec.root, path, loaded }, port, folder).catch((error: NodeJS.ErrnoException) => {
    if (error.code === "EADDRINUSE") return undefined;
    throw error;
  });
}
