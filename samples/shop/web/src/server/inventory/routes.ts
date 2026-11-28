import { Hono } from "hono";
import { z } from "zod";
import { type Env, validate } from "../platform/http.ts";
import { requireRole } from "../platform/session.ts";
import type { Inventory } from "./inventory.ts";

const delivery = z.object({
  sku: z.string().min(1, "Enter a SKU"),
  units: z.int().positive("A delivery has at least one unit"),
});

export function inventoryRoutes(inventory: Inventory) {
  return new Hono<Env>()
    .get("/stock", requireRole("customer", "staff"), validate("query", z.object({ sku: z.string() })), (c) => {
      const { sku } = c.req.valid("query");
      return c.json({ sku, onHand: inventory.onHand(sku) }, 200);
    })
    .post("/deliveries", requireRole("staff"), validate("json", delivery), (c) => {
      const { sku, units } = c.req.valid("json");
      return c.json(inventory.restock(sku, units), 201);
    });
}

export type InventoryApi = ReturnType<typeof inventoryRoutes>;
