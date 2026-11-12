import { existsSync } from "node:fs";
import { join } from "node:path";
import { loadViewModel } from "../view/load.ts";
import { serveViewer } from "../view/server.ts";

export const viewerFolder = join(import.meta.dirname, "../../dist/viewer");

export const isViewerBuilt = (folder: string): boolean => existsSync(join(folder, "index.html"));

/** Serves the viewer of the spec on `port`, and returns the server, or undefined when the port is in use. */
export async function viewSpec(spec: { readonly root: string; readonly path: string }, port: number, folder: string) {
  const loaded = await loadViewModel(spec.root, spec.path);
  return serveViewer({ ...spec, loaded }, port, folder).catch((error: NodeJS.ErrnoException) => {
    if (error.code === "EADDRINUSE") return undefined;
    throw error;
  });
}
