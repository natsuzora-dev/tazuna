import type { CancelReason, Line } from "./orders.ts";

/** The events orders publishes. Other services subscribe to them by type. */
export type OrdersEvent =
  | { type: "price.set"; data: { sku: string; price: number } }
  | { type: "order.placed"; data: { orderId: string; email: string; lines: Line[]; total: number } }
  | { type: "order.payment_requested"; data: { orderId: string; amount: number } }
  | { type: "order.confirmed"; data: { orderId: string } }
  | { type: "order.cancelled"; data: { orderId: string; reason: CancelReason } };
