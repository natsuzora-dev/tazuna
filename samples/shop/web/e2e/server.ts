// The shop for the end-to-end tests: in-memory databases, a clock the tests move, a gateway the tests answer for,
// and one recorded trace per service and test, written to TRACE_DIR for `tazuna verify`.

import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { serve } from "@hono/node-server";
import { serveStatic } from "@hono/node-server/serve-static";
import { Hono } from "hono";
import { type Outcome, SimulatedPaygate } from "../src/server/fakes/paygate.ts";
import { postWebhook } from "../src/server/fakes/webhook.ts";
import { ManualClock } from "../src/server/platform/clock.ts";
import { recordedShop, webhookSecret } from "../tazuna/recorded-shop.ts";

const port = Number(process.env.PORT ?? 4173);
const traceDir = process.env.TRACE_DIR ?? "e2e-traces";
const start = Date.UTC(2026, 0, 1, 9);
const clock = new ManualClock(start);
rmSync(traceDir, { recursive: true, force: true });

function build(title: string) {
  const paygate = new SimulatedPaygate(
    (event) => postWebhook(current.shop.app, event, webhookSecret).then(() => {}),
    "approve",
  );
  return { title, paygate, ...recordedShop({ names: ["orders", "inventory", "payments"], clock, gateway: paygate }) };
}

let current = build("before the first test");

const app = new Hono()
  .post("/__test/reset", async (c) => {
    const { title } = await c.req.json<{ title: string }>();
    clock.set(start);
    current = build(title);
    return c.body(null, 204);
  })
  .post("/__test/clock", async (c) => {
    const { advanceMs } = await c.req.json<{ advanceMs: number }>();
    clock.advance(advanceMs);
    await current.shop.tick();
    await current.shop.settled();
    return c.body(null, 204);
  })
  .put("/__test/paygate", async (c) => {
    const { autoSettle } = await c.req.json<{ autoSettle: Outcome | null }>();
    current.paygate.autoSettle = autoSettle ?? undefined;
    return c.body(null, 204);
  })
  .post("/__test/paygate/settle", async (c) => {
    const { outcome } = await c.req.json<{ outcome: Outcome }>();
    await current.paygate.settle(outcome);
    await current.shop.settled();
    return c.body(null, 204);
  })
  .post("/__test/traces", async (c) => {
    await current.shop.settled();
    for (const [service, recorder] of current.recorders) {
      if (recorder.lines.length === 1) continue;
      mkdirSync(join(traceDir, service), { recursive: true });
      const text = recorder.lines.map((line) => JSON.stringify(line)).join("\n");
      writeFileSync(join(traceDir, service, `${current.title}.jsonl`), `${text}\n`);
    }
    return c.body(null, 204);
  })
  .all("/api/*", (c) => current.shop.app.fetch(c.req.raw))
  .use("/*", serveStatic({ root: "dist" }))
  .get("/*", serveStatic({ path: "dist/index.html" }));

serve({ fetch: app.fetch, port }, () => console.info(`e2e shop on http://localhost:${port}`));
