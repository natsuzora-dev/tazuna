import { expect, it } from "vitest";
import { testShop } from "./testing.ts";

async function stockedShop() {
  const shop = testShop();
  await shop.call("staff", "POST", "/api/orders/prices", { sku: "MUG", price: 1200 });
  await shop.call("staff", "POST", "/api/inventory/deliveries", { sku: "MUG", units: 5 });
  const { body: order } = await shop.call("customer", "POST", "/api/orders/orders", {
    email: "ann@example.com",
    lines: [{ sku: "MUG", quantity: 2 }],
  });
  await shop.settled();
  return { shop, order };
}

it("confirms a paid order across the three services", async () => {
  const { shop, order } = await stockedShop();
  await shop.paygate.settle("approve");
  await shop.settled();
  expect((await shop.call("customer", "GET", `/api/orders/orders/${order.id}`)).body.status).toBe("confirmed");
  expect((await shop.call("customer", "GET", "/api/inventory/stock?sku=MUG")).body.onHand).toBe(3);
});

it("cancels an unpaid order at its deadline and puts its stock back", async () => {
  const { shop, order } = await stockedShop();
  shop.clock.advance(15 * 60_000);
  await shop.tick();
  await shop.settled();
  expect((await shop.call("customer", "GET", `/api/orders/orders/${order.id}`)).body.cancelReason).toBe(
    "payment_timeout",
  );
  expect((await shop.call("customer", "GET", "/api/inventory/stock?sku=MUG")).body.onHand).toBe(5);
  await shop.paygate.settle("approve");
  await shop.settled();
  expect((await shop.call("staff", "GET", `/api/payments/payments/${order.id}`)).body.status).toBe("refunding");
});
