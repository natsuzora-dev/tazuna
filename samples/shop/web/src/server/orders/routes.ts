import { Hono } from "hono";
import { z } from "zod";
import { type Env, problem, validate } from "../platform/http.ts";
import { requireRole } from "../platform/session.ts";
import type { Orders } from "./orders.ts";

const newPrice = z.object({
  sku: z.string().min(1, "Enter a SKU"),
  price: z.int().positive("A price must be more than zero"),
});

const newOrder = z.object({
  email: z.string().min(1, "Enter an email address"),
  lines: z
    .array(z.object({ sku: z.string(), quantity: z.int().min(1).max(10, "Order at most 10 of a product") }))
    .min(1, "Add a product to the order"),
});

export function ordersRoutes(orders: Orders) {
  return new Hono<Env>()
    .get("/prices", (c) => c.json(orders.listPrices()))
    .post("/prices", requireRole("staff"), validate("json", newPrice), (c) => {
      const { sku, price } = c.req.valid("json");
      return c.json(orders.setPrice(sku, price), 200);
    })
    .post("/orders", requireRole("customer"), validate("json", newOrder), (c) => {
      const { email, lines } = c.req.valid("json");
      const result = orders.placeOrder(email, lines);
      if (result.ok) return c.json(result.order, 201);
      return result.error === "checkout_limit_reached"
        ? problem(c, 409, result.error, "The shop is taking too many orders right now; try again soon")
        : problem(c, 422, result.error, "The order names a product the shop does not sell");
    })
    .get("/orders/:id", requireRole("customer"), (c) => {
      const order = orders.getOrder(c.req.param("id"));
      return order ? c.json(order, 200) : problem(c, 404, "order_not_found", "No such order");
    })
    .post("/orders/:id/cancel", requireRole("customer"), (c) => {
      const result = orders.cancelOrder(c.req.param("id"));
      if (result.ok) return c.body(null, 204);
      return result.error === "order_not_found"
        ? problem(c, 404, result.error, "No such order")
        : problem(c, 409, result.error, "The order can no longer be cancelled");
    });
}

export type OrdersApi = ReturnType<typeof ordersRoutes>;
