import { describe, expect, it } from "vitest";
import { testShop } from "../testing.ts";

async function shopWithStock(units: Record<string, number>) {
  const shop = testShop(["inventory"]);
  for (const [sku, n] of Object.entries(units)) {
    await shop.call("staff", "POST", "/api/inventory/deliveries", { sku, units: n });
  }
  return shop;
}

type Shop = ReturnType<typeof testShop>;

const placed = (shop: Shop, orderId: string, lines: { sku: string; quantity: number }[]) =>
  shop.inventory.handle({
    id: 0,
    type: "order.placed",
    payload: { orderId, email: "ann@example.com", lines, total: 1 },
  });

const onHand = async (shop: Shop, sku: string) =>
  (await shop.call("customer", "GET", `/api/inventory/stock?sku=${sku}`)).body.onHand;

describe("inventory", () => {
  it("adds a delivery to the stock on hand", async () => {
    const shop = await shopWithStock({ MUG: 3 });
    const response = await shop.call("staff", "POST", "/api/inventory/deliveries", { sku: "MUG", units: 2 });
    expect(response).toMatchObject({ status: 201, body: { sku: "MUG", onHand: 5 } });
    expect(await onHand(shop, "TEAPOT")).toBe(0);
  });

  it("reserves every line of an order, or none when one product is short", async () => {
    const shop = await shopWithStock({ MUG: 3, CUP: 1 });
    await placed(shop, "o1", [
      { sku: "MUG", quantity: 2 },
      { sku: "CUP", quantity: 2 },
    ]);
    await placed(shop, "o2", [
      { sku: "MUG", quantity: 2 },
      { sku: "MUG", quantity: 1 },
    ]);
    expect(shop.published(shop.inventory).slice(-2)).toEqual([
      { type: "stock.reservation_failed", data: { orderId: "o1" } },
      {
        type: "stock.reserved",
        data: {
          orderId: "o2",
          lines: [
            { sku: "MUG", quantity: 2 },
            { sku: "MUG", quantity: 1 },
          ],
        },
      },
    ]);
    expect([await onHand(shop, "MUG"), await onHand(shop, "CUP")]).toEqual([0, 1]);
  });

  it("reserves an order once, and ignores a line for no units", async () => {
    const shop = await shopWithStock({ MUG: 3 });
    await placed(shop, "o1", [{ sku: "MUG", quantity: 1 }]);
    await placed(shop, "o1", [{ sku: "MUG", quantity: 1 }]);
    await placed(shop, "o2", [{ sku: "MUG", quantity: 0 }]);
    expect(await onHand(shop, "MUG")).toBe(2);
    expect(shop.published(shop.inventory).filter((event) => event.type.startsWith("stock.reserv"))).toHaveLength(1);
  });

  it("puts a cancelled order's stock back, and keeps a confirmed order's stock off the shelf", async () => {
    const shop = await shopWithStock({ MUG: 5 });
    await placed(shop, "o1", [{ sku: "MUG", quantity: 2 }]);
    await placed(shop, "o2", [{ sku: "MUG", quantity: 3 }]);
    await shop.inventory.handle({ id: 0, type: "order.cancelled", payload: { orderId: "o1", reason: "customer" } });
    await shop.inventory.handle({ id: 0, type: "order.confirmed", payload: { orderId: "o2" } });
    await shop.inventory.handle({ id: 0, type: "order.cancelled", payload: { orderId: "o2", reason: "customer" } });
    expect(await onHand(shop, "MUG")).toBe(2);
  });
});
