import { createShop } from "./app.ts";
import { LoggingMailer } from "./fakes/mailer.ts";
import { SimulatedPaygate } from "./fakes/paygate.ts";
import { postWebhook } from "./fakes/webhook.ts";
import { inventoryService, openInventoryDb } from "./inventory/index.ts";
import { openOrdersDb, ordersService } from "./orders/index.ts";
import { openPaymentsDb, paymentsService, type WebhookEvent } from "./payments/index.ts";
import { ManualClock } from "./platform/clock.ts";
import type { Role } from "./platform/session.ts";

const webhookSecret = "test-webhook-secret";

type Name = "orders" | "inventory" | "payments";

/**
 * The shop on in-memory databases, a manual clock, and a gateway that answers only when told. With `only`, just
 * those services run, and a test plays the others by handing their events to `handle`.
 */
export function testShop(only: Name[] = ["orders", "inventory", "payments"]) {
  const clock = new ManualClock(Date.UTC(2026, 0, 1));
  const mailer = new LoggingMailer(() => {});
  const paygate = new SimulatedPaygate((event) => webhook(event).then(() => {}));
  const orders = ordersService({ db: openOrdersDb(), clock, mailer });
  const inventory = inventoryService({ db: openInventoryDb(), clock });
  const payments = paymentsService({ db: openPaymentsDb(), clock, gateway: paygate, webhookSecret });
  const shop = createShop({
    services: [orders, inventory, payments].filter((service) => only.includes(service.name as Name)),
    clock,
    sessionSecret: "test-session-secret",
  });
  const cookies = new Map<Role, string>();

  async function signIn(role: Role) {
    const cached = cookies.get(role);
    if (cached) return cached;
    const response = await shop.app.request("/api/session", {
      method: "PUT",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ role }),
    });
    const cookie = (response.headers.get("set-cookie") ?? "").split(";")[0] ?? "";
    cookies.set(role, cookie);
    return cookie;
  }

  /** Sends a request as a signed-in customer or member of staff. */
  async function call(role: Role, method: string, path: string, body?: unknown) {
    const headers: Record<string, string> = { cookie: await signIn(role) };
    if (body !== undefined) headers["content-type"] = "application/json";
    const response = await shop.app.request(path, {
      method,
      headers,
      body: body === undefined ? undefined : JSON.stringify(body),
    });
    const text = await response.text();
    return { status: response.status, body: text ? JSON.parse(text) : undefined };
  }

  const webhook = (event: WebhookEvent) => postWebhook(shop.app, event, webhookSecret);

  /** The events a service published, oldest first. */
  const published = (service: { outbox: { after(id: number): { type: string; payload: unknown }[] } }) =>
    service.outbox.after(0).map(({ type, payload }) => ({ type, data: payload }));

  return { ...shop, clock, mailer, paygate, orders, inventory, payments, call, webhook, published };
}
