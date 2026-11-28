import { describe, expect, it } from "vitest";
import { testShop } from "../testing.ts";

type Shop = ReturnType<typeof testShop>;

const due = (shop: Shop, orderId: string, amount: number) =>
  shop.payments.handle({ id: 0, type: "order.payment_requested", payload: { orderId, amount } });
const cancelled = (shop: Shop, orderId: string) =>
  shop.payments.handle({ id: 0, type: "order.cancelled", payload: { orderId, reason: "customer" } });
const status = async (shop: Shop, orderId: string) =>
  (await shop.call("staff", "GET", `/api/payments/payments/${orderId}`)).body?.status;

describe("payments", () => {
  it("charges each order once, and never for nothing", async () => {
    const shop = testShop(["payments"]);
    await due(shop, "o1", 2400);
    await due(shop, "o1", 2400);
    await due(shop, "o2", 0);
    expect(shop.paygate.requests).toEqual([{ kind: "charge", reference: "charge-o1", orderId: "o1", amount: 2400 }]);
    expect(await status(shop, "o1")).toBe("charging");
    expect((await shop.call("staff", "GET", "/api/payments/payments/o2")).status).toBe(404);
  });

  it("reports a captured or declined charge", async () => {
    const shop = testShop(["payments"]);
    await due(shop, "o1", 2400);
    await due(shop, "o2", 1200);
    await shop.paygate.settle("approve");
    await shop.paygate.settle("decline");
    expect(shop.published(shop.payments).slice(-2)).toEqual([
      { type: "payment.captured", data: { orderId: "o1", transaction: "txn_1" } },
      { type: "payment.declined", data: { orderId: "o2" } },
    ]);
  });

  it("refunds a cancelled order's charge, whether the capture comes before or after the cancellation", async () => {
    const shop = testShop(["payments"]);
    await due(shop, "before", 2400);
    await shop.paygate.settle("approve");
    await cancelled(shop, "before");
    expect(shop.paygate.requests).toEqual([
      { kind: "refund", reference: "refund-before", transaction: "txn_1", amount: 2400 },
    ]);
    await shop.paygate.settle("approve");

    await due(shop, "after", 1200);
    await cancelled(shop, "after");
    expect(await status(shop, "after")).toBe("charging");
    await shop.paygate.settle("approve");
    expect(shop.paygate.requests).toEqual([
      { kind: "refund", reference: "refund-after", transaction: "txn_2", amount: 1200 },
    ]);
    await shop.paygate.settle("decline");
    expect([await status(shop, "before"), await status(shop, "after")]).toEqual(["refunded", "refund_refused"]);
  });

  it("rejects a webhook the gateway did not sign", async () => {
    const shop = testShop(["payments"]);
    const response = await shop.app.request("/api/payments/webhooks/paygate", {
      method: "POST",
      headers: { "paygate-signature": "00" },
      body: JSON.stringify({ type: "refund.succeeded", reference: "refund-o1" }),
    });
    expect(response.status).toBe(401);
  });

  it("shows payments to staff only", async () => {
    const shop = testShop(["payments"]);
    expect((await shop.call("customer", "GET", "/api/payments/payments/o1")).status).toBe(403);
  });
});
