import { readFileSync, statSync, watch } from "node:fs";
import { createServer, type ServerResponse } from "node:http";
import type { AddressInfo } from "node:net";
import { extname, join, normalize } from "node:path";
import { type Loaded, loadViewModel } from "./load.ts";
import type { ViewEvent, ViewModel } from "./types.ts";

const contentTypes: Readonly<Record<string, string>> = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".svg": "image/svg+xml",
};

const isWatched = (file: string) => file.endsWith(".ts") || /(?:^|[\\/])__snapshots__[\\/][^\\/]+\.jsonl$/.test(file);

/** The wait after the last change event before a reload. One save fires several change events for a file. */
const settleMs = 100;

/**
 * Serves the viewer of `model` and reloads the spec on every .ts or snapshot change. A failed load keeps the last
 * model.json.
 */
export async function serveViewer(
  spec: { readonly root: string; readonly path: string; readonly cwd: string; readonly model: ViewModel },
  port: number,
  folder: string,
): Promise<{ readonly url: string; readonly closed: Promise<void>; readonly close: () => void }> {
  let body = JSON.stringify(spec.model);
  let error: string | null = null;
  const clients = new Set<ServerResponse>();
  const send = (response: ServerResponse, event: ViewEvent) => response.write(`data: ${JSON.stringify(event)}\n\n`);
  const apply = (loaded: Loaded) => {
    if ("error" in loaded) error = loaded.error;
    else {
      const next = JSON.stringify(loaded.model);
      if (next === body && error === null) return;
      body = next;
      error = null;
    }
    const event: ViewEvent = error === null ? { type: "model" } : { type: "error", message: error };
    for (const client of clients) send(client, event);
  };
  let loading = false;
  let again = false;
  const reload = async () => {
    if (loading) {
      again = true;
      return;
    }
    loading = true;
    do {
      again = false;
      apply(await loadViewModel(spec.root, spec.path, spec.cwd));
    } while (again);
    loading = false;
  };
  let timer: NodeJS.Timeout | undefined;
  const watcher = watch(spec.root, { recursive: true }, (_, file) => {
    if (file === null || !isWatched(file)) return;
    clearTimeout(timer);
    timer = setTimeout(reload, settleMs);
  });
  const server = createServer((request, response) => {
    const url = URL.parse(request.url ?? "/", "http://localhost");
    if (url === null) {
      response.writeHead(400).end();
      return;
    }
    if (url.pathname === "/model.json") {
      response.writeHead(200, { "content-type": "application/json; charset=utf-8" }).end(body);
      return;
    }
    if (url.pathname === "/events") {
      // Firefox fires EventSource open only after body bytes arrive, so a comment line goes out at once.
      response
        .writeHead(200, { "content-type": "text/event-stream", "cache-control": "no-cache" })
        .write(": connected\n\n");
      if (error !== null) send(response, { type: "error", message: error });
      clients.add(response);
      request.on("close", () => clients.delete(response));
      return;
    }
    const file = join(folder, normalize(url.pathname === "/" ? "/index.html" : url.pathname));
    if (!file.startsWith(folder) || !statSync(file, { throwIfNoEntry: false })?.isFile()) {
      response.writeHead(404).end();
      return;
    }
    response
      .writeHead(200, { "content-type": contentTypes[extname(file)] ?? "application/octet-stream" })
      .end(readFileSync(file));
  });
  const closed = new Promise<void>((resolve) => server.on("close", resolve));
  const close = () => {
    watcher.close();
    clearTimeout(timer);
    server.close();
    server.closeAllConnections();
  };
  await new Promise<void>((resolve, reject) => {
    server.once("error", (e) => {
      watcher.close();
      reject(e);
    });
    server.listen(port, "localhost", resolve);
  });
  return { url: `http://localhost:${(server.address() as AddressInfo).port}/`, closed, close };
}
