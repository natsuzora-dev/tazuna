import { z } from "zod";
import type { Clock } from "../platform/clock.ts";
import { outboxReader } from "../platform/outbox.ts";
import { consumer, on, type Service } from "../platform/service.ts";
import { createInventory, type InventoryDb } from "./inventory.ts";
import { type InventoryApi, inventoryRoutes } from "./routes.ts";

export { openInventoryDb } from "./inventory.ts";
export type { InventoryApi } from "./routes.ts";

const aboutOrder = z.object({ orderId: z.string() });
const placed = aboutOrder.extend({ lines: z.array(z.object({ sku: z.string(), quantity: z.int() })) });

export function inventoryService(deps: { db: InventoryDb; clock: Clock }): Service<InventoryApi> {
  const inventory = createInventory(deps);
  return {
    name: "inventory",
    routes: inventoryRoutes(inventory),
    ...consumer({
      "order.placed": on(placed, ({ orderId, lines }) => inventory.reserve(orderId, lines)),
      "order.confirmed": on(aboutOrder, ({ orderId }) => inventory.commit(orderId)),
      "order.cancelled": on(aboutOrder, ({ orderId }) => inventory.release(orderId)),
    }),
    tick: async () => {},
    outbox: outboxReader(deps.db),
  };
}
