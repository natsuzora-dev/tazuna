import { Hono } from "hono";
import { type Env, problem } from "../platform/http.ts";
import { requireRole } from "../platform/session.ts";
import { signatureHeader, verifySignature, webhookEvent } from "./gateway.ts";
import type { Payments } from "./payments.ts";

export function paymentsRoutes(payments: Payments, webhookSecret: string) {
  return new Hono<Env>()
    .get("/payments/:orderId", requireRole("staff"), (c) => {
      const payment = payments.get(c.req.param("orderId"));
      if (!payment) return problem(c, 404, "payment_not_found", "No payment for this order");
      const { orderId, amountCents, status, transactionId, orderCancelled } = payment;
      return c.json({ orderId, amount: amountCents, status, transactionId, orderCancelled }, 200);
    })
    .post("/webhooks/paygate", async (c) => {
      const body = await c.req.text();
      if (!verifySignature(body, c.req.header(signatureHeader), webhookSecret)) {
        return problem(c, 401, "bad_signature", "The webhook signature does not match");
      }
      const event = webhookEvent.safeParse(JSON.parse(body));
      if (!event.success) return problem(c, 400, "validation_failed", "Unknown webhook event");
      if (!payments.gatewayReported(event.data)) return problem(c, 404, "payment_not_found", "Unknown reference");
      return c.json({ received: true }, 200);
    });
}

export type PaymentsApi = ReturnType<typeof paymentsRoutes>;
