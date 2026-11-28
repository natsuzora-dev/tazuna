import { z } from "zod";
import type { Clock } from "../platform/clock.ts";
import { outboxReader } from "../platform/outbox.ts";
import { consumer, on, type Service } from "../platform/service.ts";
import type { PaymentGateway } from "./gateway.ts";
import { createPayments, type PaymentsDb } from "./payments.ts";
import { type PaymentsApi, paymentsRoutes } from "./routes.ts";

export type { PaymentGateway, WebhookEvent } from "./gateway.ts";
export { sign, signatureHeader } from "./gateway.ts";
export { openPaymentsDb } from "./payments.ts";
export type { PaymentsApi } from "./routes.ts";

export function paymentsService(deps: {
  db: PaymentsDb;
  clock: Clock;
  gateway: PaymentGateway;
  webhookSecret: string;
}): Service<PaymentsApi> {
  const payments = createPayments(deps);
  return {
    name: "payments",
    routes: paymentsRoutes(payments, deps.webhookSecret),
    ...consumer({
      "order.payment_requested": on(z.object({ orderId: z.string(), amount: z.int() }), ({ orderId, amount }) =>
        payments.charge(orderId, amount),
      ),
      "order.cancelled": on(z.object({ orderId: z.string() }), ({ orderId }) => payments.orderCancelled(orderId)),
    }),
    tick: async () => {},
    outbox: outboxReader(deps.db),
  };
}
