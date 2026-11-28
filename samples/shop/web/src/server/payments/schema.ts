import { sql } from "drizzle-orm";
import { check, integer, sqliteTable, text } from "drizzle-orm/sqlite-core";

export { outbox } from "../platform/outbox.ts";

export const paymentStatuses = [
  "charging",
  "captured",
  "declined",
  "refunding",
  "refunded",
  /** The gateway refused the refund; staff refund the customer by hand. */
  "refund_refused",
] as const;

/** One charge per order, and its refund if the order is cancelled. */
export const payments = sqliteTable(
  "payments",
  {
    orderId: text().primaryKey(),
    amountCents: integer().notNull(),
    status: text({ enum: paymentStatuses }).notNull(),
    /** The gateway's id for the captured charge. */
    transactionId: text(),
    orderCancelled: integer({ mode: "boolean" }).notNull().default(false),
    chargeReference: text().notNull().unique(),
    refundReference: text().unique(),
    createdAt: integer().notNull(),
  },
  (t) => [
    check("payments_amount", sql`${t.amountCents} > 0`),
    check(
      "payments_transaction",
      sql`${t.status} not in ('captured', 'refunding', 'refund_refused') or ${t.transactionId} is not null`,
    ),
  ],
);
