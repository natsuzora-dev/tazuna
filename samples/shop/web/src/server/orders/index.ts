import { z } from "zod";
import type { Clock } from "../platform/clock.ts";
import { outboxReader } from "../platform/outbox.ts";
import { consumer, on, type Service } from "../platform/service.ts";
import { createOrders, type Mailer, type OrdersDb } from "./orders.ts";
import { type OrdersApi, ordersRoutes } from "./routes.ts";

export type { Mail, Mailer } from "./orders.ts";
export { openOrdersDb } from "./orders.ts";
export type { OrdersApi } from "./routes.ts";

const aboutOrder = z.object({ orderId: z.string() });

export function ordersService(deps: { db: OrdersDb; clock: Clock; mailer: Mailer }): Service<OrdersApi> {
  const orders = createOrders(deps);
  return {
    name: "orders",
    routes: ordersRoutes(orders),
    ...consumer({
      "stock.reserved": on(aboutOrder, ({ orderId }) => orders.stockReserved(orderId)),
      "stock.reservation_failed": on(aboutOrder, ({ orderId }) => orders.stockUnavailable(orderId)),
      "payment.captured": on(aboutOrder, ({ orderId }) => orders.paymentCaptured(orderId)),
      "payment.declined": on(aboutOrder, ({ orderId }) => orders.paymentFailed(orderId)),
    }),
    tick: async () => orders.expireUnpaidOrders(),
    outbox: outboxReader(deps.db),
  };
}
