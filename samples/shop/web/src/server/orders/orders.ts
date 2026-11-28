import { randomUUID } from "node:crypto";
import { and, asc, count, eq, inArray, lte } from "drizzle-orm";
import type { Clock } from "../platform/clock.ts";
import { openDatabase } from "../platform/db.ts";
import { publish } from "../platform/outbox.ts";
import type { OrdersEvent } from "./events.ts";
import * as schema from "./schema.ts";
import { type cancelReasons, orderLines, type orderStatuses, orders, prices } from "./schema.ts";

export type OrderStatus = (typeof orderStatuses)[number];
export type CancelReason = (typeof cancelReasons)[number];

export interface Line {
  sku: string;
  quantity: number;
}

/** The shop takes at most this many orders that wait for stock or payment at a time. */
export const MAX_OPEN_CHECKOUTS = 3;
/** How long a customer has to pay after placing an order. */
export const TIME_TO_PAY_MS = 15 * 60_000;

const openStatuses: readonly OrderStatus[] = ["awaiting_stock", "awaiting_payment"];

/** The order lifecycle: the statuses each move starts from, and the status it ends in. */
const moves = {
  requestPayment: { from: ["awaiting_stock"], to: "awaiting_payment" },
  confirm: { from: ["awaiting_payment"], to: "confirmed" },
  cancel: { from: openStatuses, to: "cancelled" },
} as const satisfies Record<string, { from: readonly OrderStatus[]; to: OrderStatus }>;

export interface Mail {
  to: string;
  subject: string;
  text: string;
}

export interface Mailer {
  send(mail: Mail): Promise<void>;
}

export function openOrdersDb(file = ":memory:") {
  return openDatabase(file, schema, `${import.meta.dirname}/migrations`);
}

export type OrdersDb = ReturnType<typeof openOrdersDb>;
type Tx = Parameters<Parameters<OrdersDb["transaction"]>[0]>[0];
type OrderRow = typeof orders.$inferSelect;

export function createOrders({ db, clock, mailer }: { db: OrdersDb; clock: Clock; mailer: Mailer }) {
  const emit = (tx: Tx, event: OrdersEvent) => publish(tx, event, clock.now());

  const find = (tx: Tx | OrdersDb, id: string) => tx.select().from(orders).where(eq(orders.id, id)).get();

  function move(tx: Tx, order: OrderRow, name: keyof typeof moves, cancelReason: CancelReason | null = null) {
    if (!(moves[name].from as readonly OrderStatus[]).includes(order.status)) return false;
    tx.update(orders).set({ status: moves[name].to, cancelReason }).where(eq(orders.id, order.id)).run();
    return true;
  }

  function cancel(tx: Tx, order: OrderRow, reason: CancelReason) {
    if (!move(tx, order, "cancel", reason)) return false;
    emit(tx, { type: "order.cancelled", data: { orderId: order.id, reason } });
    return true;
  }

  function mail(order: OrderRow, subject: string) {
    const text = `${subject}. Order ${order.id}, total ${(order.totalCents / 100).toFixed(2)}.`;
    mailer.send({ to: order.email, subject, text }).catch((error) => console.error("mail not sent", error));
  }

  const mailCancelled = (order: OrderRow) => mail(order, "Your order is cancelled");

  /** Cancels an open order for one of the shop's reasons, and tells the customer. */
  function cancelFor(orderId: string, reason: CancelReason) {
    const cancelled = db.transaction((tx) => {
      const order = find(tx, orderId);
      return order && cancel(tx, order, reason) ? order : undefined;
    });
    if (cancelled) mailCancelled(cancelled);
  }

  function view(order: OrderRow, lines: Line[]) {
    const { id, email, totalCents, status, cancelReason, placedAt, payBy } = order;
    return { id, email, lines, total: totalCents, status, cancelReason, placedAt, payBy };
  }

  return {
    listPrices: () =>
      db.select({ sku: prices.sku, price: prices.priceCents }).from(prices).orderBy(asc(prices.sku)).all(),

    setPrice(sku: string, price: number) {
      db.transaction((tx) => {
        tx.insert(prices)
          .values({ sku, priceCents: price })
          .onConflictDoUpdate({ target: prices.sku, set: { priceCents: price } })
          .run();
        emit(tx, { type: "price.set", data: { sku, price } });
      });
      return { sku, price };
    },

    placeOrder(email: string, lines: Line[]) {
      return db.transaction((tx) => {
        const open = tx.select({ n: count() }).from(orders).where(inArray(orders.status, openStatuses)).get();
        if ((open?.n ?? 0) >= MAX_OPEN_CHECKOUTS) return { ok: false, error: "checkout_limit_reached" } as const;
        const skus = [...new Set(lines.map((line) => line.sku))];
        const priceOf = new Map(
          tx
            .select()
            .from(prices)
            .where(inArray(prices.sku, skus))
            .all()
            .map((row) => [row.sku, row.priceCents]),
        );
        if (!skus.every((sku) => priceOf.has(sku))) return { ok: false, error: "unknown_product" } as const;

        const now = clock.now();
        const order: OrderRow = {
          id: randomUUID(),
          email,
          totalCents: lines.reduce((sum, line) => sum + line.quantity * (priceOf.get(line.sku) ?? 0), 0),
          status: "awaiting_stock",
          cancelReason: null,
          placedAt: now,
          payBy: now + TIME_TO_PAY_MS,
        };
        tx.insert(orders).values(order).run();
        tx.insert(orderLines)
          .values(lines.map((line, position) => ({ orderId: order.id, position, ...line })))
          .run();
        emit(tx, { type: "order.placed", data: { orderId: order.id, email, lines, total: order.totalCents } });
        return { ok: true, order: view(order, lines) } as const;
      });
    },

    getOrder(id: string) {
      const order = find(db, id);
      if (!order) return undefined;
      const lines = db
        .select({ sku: orderLines.sku, quantity: orderLines.quantity })
        .from(orderLines)
        .where(eq(orderLines.orderId, id))
        .orderBy(asc(orderLines.position))
        .all();
      return view(order, lines);
    },

    /** The customer cancels an order that still waits for stock or payment. */
    cancelOrder(id: string) {
      const result = db.transaction((tx) => {
        const order = find(tx, id);
        if (!order) return { ok: false, error: "order_not_found" } as const;
        if (!cancel(tx, order, "customer")) return { ok: false, error: "order_not_open" } as const;
        return { ok: true, order } as const;
      });
      if (result.ok) mailCancelled(result.order);
      return result;
    },

    /** Inventory holds the stock, so the order waits for payment. */
    stockReserved(orderId: string) {
      db.transaction((tx) => {
        const order = find(tx, orderId);
        if (order && move(tx, order, "requestPayment")) {
          emit(tx, { type: "order.payment_requested", data: { orderId, amount: order.totalCents } });
        }
      });
    },

    stockUnavailable: (orderId: string) => cancelFor(orderId, "out_of_stock"),

    paymentCaptured(orderId: string) {
      const confirmed = db.transaction((tx) => {
        const order = find(tx, orderId);
        if (!order || !move(tx, order, "confirm")) return undefined;
        emit(tx, { type: "order.confirmed", data: { orderId } });
        return order;
      });
      if (confirmed) mail(confirmed, "Your order is confirmed");
    },

    paymentFailed: (orderId: string) => cancelFor(orderId, "payment_failed"),

    /** Cancels every open order whose time to pay has run out. */
    expireUnpaidOrders() {
      const expired = db.transaction((tx) =>
        tx
          .select()
          .from(orders)
          .where(and(inArray(orders.status, openStatuses), lte(orders.payBy, clock.now())))
          .all()
          .filter((order) => cancel(tx, order, "payment_timeout")),
      );
      expired.forEach(mailCancelled);
    },
  };
}

export type Orders = ReturnType<typeof createOrders>;
