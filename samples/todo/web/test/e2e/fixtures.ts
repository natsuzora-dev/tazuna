import { join } from "node:path";
import type { AnyProcedure, AnyRouter } from "@orpc/server";
import { test as base, expect } from "@playwright/test";
import { tanstackStart } from "@tanstack/react-start/plugin/vite";
import basicSsl from "@vitejs/plugin-basic-ssl";
import viteReact from "@vitejs/plugin-react";
import { migrate } from "drizzle-orm/node-sqlite/migrator";
import {
  createServer,
  defaultClientConditions,
  defaultServerConditions,
  isRunnableDevEnvironment,
  type Plugin,
} from "vite";
import type { ModuleRunner } from "vite/module-runner";
import type * as Db from "../../src/db/index.server.ts";
import type * as Notifier from "../../src/notifier/notifier.server.ts";
import type * as TodoRouter from "../../src/todo/todo.router.ts";
import type * as Held from "../doubles/held.ts";
import type * as NotifierDouble from "../doubles/notifier.ts";
import type * as TodoRouterDouble from "../doubles/todoRouter.ts";

const web = join(import.meta.dirname, "../..");

type DoubleOf<Real> = {
  readonly [K in keyof Real]: Real[K] extends (...args: infer A) => infer R
    ? (...args: A) => R
    : Real[K] extends AnyRouter
      ? { readonly [P in keyof Real[K]]: AnyProcedure }
      : Real[K];
};

const double = <Real, _Double extends DoubleOf<Real>>(real: string, double: string): [string, string] => [
  join(web, real),
  join(web, double),
];

const doubles = new Map([
  double<typeof TodoRouter, typeof TodoRouterDouble>("src/todo/todo.router.ts", "test/doubles/todoRouter.ts"),
  double<typeof Notifier, typeof NotifierDouble>("src/notifier/notifier.server.ts", "test/doubles/notifier.ts"),
]);

const useDoubles: Plugin = {
  name: "use-doubles",
  enforce: "pre",
  async resolveId(source, importer) {
    const resolved = await this.resolve(source, importer, { skipSelf: true });
    const double = resolved && doubles.get(resolved.id.split("?")[0] ?? "");
    return double === importer ? null : double;
  },
};

export interface App {
  readonly url: string;
  readonly runner: ModuleRunner;
}

/**
 * The app runs in the test process, not as a webServer, because tests hand answers to the doubles in process. The Nitro
 * plugin runs the server in another thread, so vite.config.ts is not loaded and the other plugins are listed here. The
 * server uses HTTPS so that Vite serves HTTP/2: over HTTP/1.1, Chromium opens at most 6 connections to a host, the
 * detail screen's subscriptions hold 5 of them, and a command waits for a free connection.
 */
export const test = base.extend<{ held: typeof Held }, { app: App }>({
  app: [
    // biome-ignore lint/correctness/noEmptyPattern: Playwright reads a fixture's dependencies from the first argument's destructuring
    async ({}, use, workerInfo) => {
      process.env["DB_FILE_NAME"] = ":memory:";
      const port = 3100 + workerInfo.parallelIndex;
      const vite = await createServer({
        configFile: false,
        root: web,
        cacheDir: join(web, `node_modules/.vite-e2e-${workerInfo.parallelIndex}`),
        logLevel: "warn",
        plugins: [tanstackStart(), viteReact(), basicSsl(), useDoubles],
        resolve: { conditions: ["tazuna:source", ...defaultClientConditions] },
        ssr: { resolve: { conditions: ["tazuna:source", ...defaultServerConditions] } },
        server: { port, strictPort: true, hmr: false, watch: null },
      });
      await vite.listen();
      const ssr = vite.environments["ssr"];
      if (ssr === undefined || !isRunnableDevEnvironment(ssr))
        throw new Error("the ssr environment cannot run modules");
      const { db } = await ssr.runner.import<typeof Db>("/src/db/index.server.ts");
      migrate(db, { migrationsFolder: join(web, "drizzle") });
      await use({ url: `https://localhost:${port}`, runner: ssr.runner });
      await vite.close();
    },
    { scope: "worker" },
  ],
  baseURL: async ({ app }, use) => use(app.url),
  held: async ({ app }, use) => {
    const held = await app.runner.import<typeof Held>("/test/doubles/held.ts");
    await use(held);
    held.whenHeld({});
  },
  page: async ({ page, app }, use) => {
    const errors: string[] = [];
    // Chromium logs error status responses as console errors, so command rejections are checked in the trace instead.
    page.on("console", (message) => {
      if (message.type() === "error" && !message.location().url.startsWith(`${app.url}/api/rpc/`))
        errors.push(message.text());
    });
    page.on("pageerror", (error) => errors.push(error.message));
    await use(page);
    expect(errors).toEqual([]);
  },
});
