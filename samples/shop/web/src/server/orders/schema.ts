import { sql } from "drizzle-orm";
import { check, index, integer, primaryKey, sqliteTable, text } from "drizzle-orm/sqlite-core";

export { outbox } from "../platform/outbox.ts";

export const orderStatuses = ["awaiting_stock", "awaiting_payment", "confirmed", "cancelled"] as const;
export const cancelReasons = ["customer", "out_of_stock", "payment_failed", "payment_timeout"] as const;

/** The price list, in cents. */
export const prices = sqliteTable("prices", {
  sku: text().primaryKey(),
  priceCents: integer().notNull(),
});

export const orders = sqliteTable(
  "orders",
  {
    id: text().primaryKey(),
    email: text().notNull(),
    totalCents: integer().notNull(),
    status: text({ enum: orderStatuses }).notNull(),
    cancelReason: text({ enum: cancelReasons }),
    placedAt: integer().notNull(),
    payBy: integer().notNull(),
  },
  (t) => [
    index("orders_status_pay_by").on(t.status, t.payBy),
    check("orders_cancel_reason", sql`(${t.status} = 'cancelled') = (${t.cancelReason} is not null)`),
  ],
);

export const orderLines = sqliteTable(
  "order_lines",
  {
    orderId: text()
      .notNull()
      .references(() => orders.id),
    position: integer().notNull(),
    sku: text().notNull(),
    quantity: integer().notNull(),
  },
  (t) => [primaryKey({ columns: [t.orderId, t.position] })],
);
