import assert from "node:assert/strict";
import { appendFileSync, cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { get } from "node:http";
import { join } from "node:path";
import { test } from "node:test";
import { loadViewModel } from "../../src/view/load.ts";
import { serveViewer } from "../../src/view/server.ts";
import type { ViewEvent, ViewModel } from "../../src/view/types.ts";

/** Returns with /events already open, so no change notice after the return is missed. */
async function listen(url: string): Promise<AsyncGenerator<ViewEvent>> {
  const response = await fetch(`${url}events`);
  return (async function* () {
    const decoder = new TextDecoder();
    let buffer = "";
    for await (const chunk of response.body as AsyncIterable<Uint8Array>) {
      buffer += decoder.decode(chunk, { stream: true });
      for (let end = buffer.indexOf("\n\n"); end !== -1; end = buffer.indexOf("\n\n")) {
        const block = buffer.slice(0, end);
        buffer = buffer.slice(end + 2);
        // A block without data, such as a comment line that starts with ":", is skipped, as EventSource does.
        if (block.startsWith("data: ")) yield JSON.parse(block.slice("data: ".length));
      }
    }
  })();
}

async function withCopy(body: (copy: string, viewer: string) => Promise<void>): Promise<void> {
  mkdirSync(join(import.meta.dirname, "../.fixtures"), { recursive: true });
  const copy = mkdtempSync(join(import.meta.dirname, "../.fixtures", "watch-"));
  const viewer = mkdtempSync(join(import.meta.dirname, "../.fixtures", "viewer-"));
  try {
    writeFileSync(join(viewer, "index.html"), "");
    cpSync(join(import.meta.dirname, "../../samples/todo/spec"), copy, { recursive: true });
    // tsc's include skips the dot folder .fixtures, so the copy gets a tsconfig.json of its own.
    writeFileSync(join(copy, "tsconfig.json"), '{ "extends": "../../../tsconfig.json", "include": ["."] }\n');
    await body(copy, viewer);
  } finally {
    rmSync(copy, { recursive: true, force: true });
    rmSync(viewer, { recursive: true, force: true });
  }
}

test("The view server reloads the spec in a child process when a spec file changes and notifies /events, keeps the old model.json and notifies the reason when loading fails, and recovers when loading succeeds", async () => {
  await withCopy(async (copy, viewer) => {
    const data = join(copy, "todo/data.ts");
    const loaded = await loadViewModel(copy, "copy", process.cwd());
    assert.ok("model" in loaded);
    const server = await serveViewer({ root: copy, path: "copy", cwd: process.cwd(), model: loaded.model }, 0, viewer);
    try {
      const task = async () => {
        const model = (await (await fetch(`${server.url}model.json`)).json()) as ViewModel;
        const definition = model.services.find((s) => s.name === "todo")?.definitions.find((d) => d.name === "Task");
        return (definition?.definition as Readonly<Record<string, unknown>> | undefined)?.["description"];
      };
      const watching = await listen(server.url);
      const original = readFileSync(data, "utf8");
      writeFileSync(
        data,
        original.replace('description: "A task of the user",', 'description: "A to-do of the user",'),
      );
      assert.deepEqual((await watching.next()).value, { type: "model" });
      assert.equal(await task(), "A to-do of the user");

      appendFileSync(data, "const broken = ;\n");
      const failed = (await watching.next()).value;
      assert.equal(failed?.type, "error");
      assert.match(
        failed?.type === "error" ? failed.message : "",
        /"data":\{"code":"TS1109","message":"Expression expected\."\},"location":\{"file":"todo\/data\.ts"/,
      );
      assert.equal(await task(), "A to-do of the user");
      assert.deepEqual((await (await listen(server.url)).next()).value, failed);

      writeFileSync(data, original);
      assert.deepEqual((await watching.next()).value, { type: "model" });
      assert.equal(await task(), "A task of the user");
    } finally {
      server.close();
    }
  });
});

test("The view server answers 400 to a request whose path is no URL path, such as //, and keeps serving", async () => {
  mkdirSync(join(import.meta.dirname, "../.fixtures"), { recursive: true });
  const viewer = mkdtempSync(join(import.meta.dirname, "../.fixtures", "viewer-"));
  writeFileSync(join(viewer, "index.html"), "");
  const model = { spec: "viewer", services: [], scenarios: [] };
  const server = await serveViewer({ root: viewer, path: "viewer", cwd: process.cwd(), model }, 0, viewer);
  try {
    const status = await new Promise<number | undefined>((resolve, reject) =>
      get(new URL(server.url), { path: "//" }, (response) => {
        response.resume();
        resolve(response.statusCode);
      }).on("error", reject),
    );
    assert.equal(status, 400);
    assert.equal((await fetch(server.url)).status, 200);
  } finally {
    server.close();
    rmSync(viewer, { recursive: true, force: true });
  }
});
