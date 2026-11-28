import { describe, expect, it } from "vitest";
import { testShop } from "../testing.ts";

async function shopWithMugs() {
  const shop = testShop(["orders"]);
  await shop.call("staff", "POST", "/api/orders/prices", { sku: "MUG", price: 1200 });
  return shop;
}

const twoMugs = { email: "ann@example.com", lines: [{ sku: "MUG", quantity: 2 }] };

function deliver(shop: ReturnType<typeof testShop>, type: string, orderId: string) {
  return shop.orders.handle({ id: 0, type, payload: { orderId } });
}

describe("orders", () => {
  it("prices a new order from the price list and gives the customer 15 minutes to pay", async () => {
    const shop = await shopWithMugs();
    const placed = await shop.call("customer", "POST", "/api/orders/orders", twoMugs);
    expect(placed.status).toBe(201);
    expect(placed.body).toMatchObject({ total: 2400, status: "awaiting_stock", payBy: shop.clock.now() + 900_000 });
    expect(shop.published(shop.orders).at(-1)).toEqual({
      type: "order.placed",
      data: { orderId: placed.body.id, email: "ann@example.com", lines: twoMugs.lines, total: 2400 },
    });
  });

  it("reports every invalid field at once", async () => {
    const shop = await shopWithMugs();
    const response = await shop.call("customer", "POST", "/api/orders/orders", {
      email: "",
      lines: [{ sku: "MUG", quantity: 11 }],
    });
    expect(response.status).toBe(400);
    expect(response.body.errors.map((error: { path: string }) => error.path)).toEqual(["email", "lines.0.quantity"]);
  });

  it("lets only staff set prices", async () => {
    const shop = testShop(["orders"]);
    const response = await shop.call("customer", "POST", "/api/orders/prices", { sku: "MUG", price: 1200 });
    expect(response.status).toBe(403);
  });

  it("takes three open orders at a time, and says so before it checks the products", async () => {
    const shop = await shopWithMugs();
    for (let i = 0; i < 3; i++) await shop.call("customer", "POST", "/api/orders/orders", twoMugs);
    const fourth = await shop.call("customer", "POST", "/api/orders/orders", {
      ...twoMugs,
      lines: [{ sku: "TEAPOT", quantity: 1 }],
    });
    expect(fourth).toMatchObject({ status: 409, body: { type: "checkout_limit_reached" } });
  });

  it("refuses a product that has no price", async () => {
    const shop = await shopWithMugs();
    const response = await shop.call("customer", "POST", "/api/orders/orders", {
      ...twoMugs,
      lines: [{ sku: "TEAPOT", quantity: 1 }],
    });
    expect(response).toMatchObject({ status: 422, body: { type: "unknown_product" } });
  });

  it("asks for payment once the stock is held, confirms a paid order, and mails the customer", async () => {
    const shop = await shopWithMugs();
    const { body: order } = await shop.call("customer", "POST", "/api/orders/orders", twoMugs);
    await deliver(shop, "stock.reserved", order.id);
    expect(shop.published(shop.orders).at(-1)).toEqual({
      type: "order.payment_requested",
      data: { orderId: order.id, amount: 2400 },
    });
    await deliver(shop, "payment.captured", order.id);
    const status = await shop.call("customer", "GET", `/api/orders/orders/${order.id}`);
    expect(status.body.status).toBe("confirmed");
    expect(shop.mailer.sent).toMatchObject([{ to: "ann@example.com", subject: "Your order is confirmed" }]);
  });

  it("cancels an order that is not paid by its deadline, and no earlier", async () => {
    const shop = await shopWithMugs();
    const { body: order } = await shop.call("customer", "POST", "/api/orders/orders", twoMugs);
    await deliver(shop, "stock.reserved", order.id);

    shop.clock.advance(900_000 - 1);
    await shop.tick();
    expect((await shop.call("customer", "GET", `/api/orders/orders/${order.id}`)).body.status).toBe("awaiting_payment");

    shop.clock.advance(1);
    await shop.tick();
    const status = await shop.call("customer", "GET", `/api/orders/orders/${order.id}`);
    expect(status.body).toMatchObject({ status: "cancelled", cancelReason: "payment_timeout" });
    expect(shop.mailer.sent).toMatchObject([{ to: "ann@example.com", subject: "Your order is cancelled" }]);
  });

  it("cancels an order for the customer while it is open", async () => {
    const shop = await shopWithMugs();
    const { body: order } = await shop.call("customer", "POST", "/api/orders/orders", twoMugs);
    expect((await shop.call("customer", "POST", `/api/orders/orders/${order.id}/cancel`)).status).toBe(204);
    expect(await shop.call("customer", "POST", `/api/orders/orders/${order.id}/cancel`)).toMatchObject({
      status: 409,
      body: { type: "order_not_open" },
    });
    expect((await shop.call("customer", "POST", "/api/orders/orders/nope/cancel")).status).toBe(404);
  });

  it("cancels an order when stock is short or the payment fails", async () => {
    const shop = await shopWithMugs();
    const { body: short } = await shop.call("customer", "POST", "/api/orders/orders", twoMugs);
    const { body: unpaid } = await shop.call("customer", "POST", "/api/orders/orders", twoMugs);
    await deliver(shop, "stock.reservation_failed", short.id);
    await deliver(shop, "stock.reserved", unpaid.id);
    await deliver(shop, "payment.declined", unpaid.id);
    expect((await shop.call("customer", "GET", `/api/orders/orders/${short.id}`)).body.cancelReason).toBe(
      "out_of_stock",
    );
    expect((await shop.call("customer", "GET", `/api/orders/orders/${unpaid.id}`)).body.cancelReason).toBe(
      "payment_failed",
    );
  });
});
