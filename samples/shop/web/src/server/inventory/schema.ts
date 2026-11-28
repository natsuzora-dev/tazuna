import { sql } from "drizzle-orm";
import { check, integer, primaryKey, sqliteTable, text } from "drizzle-orm/sqlite-core";

export { outbox } from "../platform/outbox.ts";

/** Units on the shelf per product. */
export const stock = sqliteTable("stock", { sku: text().primaryKey(), onHand: integer().notNull() }, (t) => [
  check("stock_on_hand", sql`${t.onHand} >= 0`),
]);

/** Stock taken off the shelf for an order until the order is confirmed or cancelled. */
export const reservations = sqliteTable("reservations", {
  orderId: text().primaryKey(),
  reservedAt: integer().notNull(),
});

export const reservationLines = sqliteTable(
  "reservation_lines",
  {
    orderId: text()
      .notNull()
      .references(() => reservations.orderId, { onDelete: "cascade" }),
    position: integer().notNull(),
    sku: text().notNull(),
    quantity: integer().notNull(),
  },
  (t) => [primaryKey({ columns: [t.orderId, t.position] }), check("reservation_quantity", sql`${t.quantity} > 0`)],
);
