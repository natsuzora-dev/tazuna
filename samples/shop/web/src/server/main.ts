import { mkdirSync } from "node:fs";
import { serve } from "@hono/node-server";
import { serveStatic } from "@hono/node-server/serve-static";
import { createShop } from "./app.ts";
import { LoggingMailer } from "./fakes/mailer.ts";
import { SimulatedPaygate } from "./fakes/paygate.ts";
import { postWebhook } from "./fakes/webhook.ts";
import { inventoryService, openInventoryDb } from "./inventory/index.ts";
import { openOrdersDb, ordersService } from "./orders/index.ts";
import { openPaymentsDb, paymentsService } from "./payments/index.ts";
import { systemClock } from "./platform/clock.ts";

const env = {
  port: Number(process.env.PORT ?? 3000),
  dataDir: process.env.DATA_DIR ?? "data",
  sessionSecret: process.env.SESSION_SECRET ?? "dev-session-secret",
  webhookSecret: process.env.PAYGATE_WEBHOOK_SECRET ?? "dev-webhook-secret",
};

mkdirSync(env.dataDir, { recursive: true });
const clock = systemClock;
const paygate = new SimulatedPaygate(
  (event) => postWebhook(shop.app, event, env.webhookSecret).then(() => {}),
  "approve",
);
const shop = createShop({
  clock,
  sessionSecret: env.sessionSecret,
  services: [
    ordersService({ db: openOrdersDb(`${env.dataDir}/orders.db`), clock, mailer: new LoggingMailer() }),
    inventoryService({ db: openInventoryDb(`${env.dataDir}/inventory.db`), clock }),
    paymentsService({
      db: openPaymentsDb(`${env.dataDir}/payments.db`),
      clock,
      gateway: paygate,
      webhookSecret: env.webhookSecret,
    }),
  ],
});

shop.app.use("/*", serveStatic({ root: "dist" })).get("/*", serveStatic({ path: "dist/index.html" }));
setInterval(() => void shop.tick(), 5_000);
serve({ fetch: shop.app.fetch, port: env.port }, ({ port }) => console.info(`shop on http://localhost:${port}`));
