import { createHmac, timingSafeEqual } from "node:crypto";
import { z } from "zod";

/**
 * The payment gateway's API as the shop uses it. A charge or refund request returns at once; the gateway reports
 * the outcome later through a webhook that names the request's reference.
 */
export interface PaymentGateway {
  createCharge(request: { reference: string; orderId: string; amount: number }): Promise<void>;
  createRefund(request: { reference: string; transaction: string; amount: number }): Promise<void>;
}

export const webhookEvent = z.discriminatedUnion("type", [
  z.object({ type: z.literal("charge.succeeded"), reference: z.string(), transaction: z.string() }),
  z.object({
    type: z.literal("charge.failed"),
    reference: z.string(),
    failureCode: z.enum(["card_declined", "insufficient_funds"]),
  }),
  z.object({ type: z.literal("refund.succeeded"), reference: z.string() }),
  z.object({ type: z.literal("refund.failed"), reference: z.string(), failureCode: z.enum(["refund_window_closed"]) }),
]);

export type WebhookEvent = z.infer<typeof webhookEvent>;

export const signatureHeader = "paygate-signature";

/** The webhook signature: an HMAC-SHA256 of the raw body with the shared secret, in hex. */
export function sign(body: string, secret: string): string {
  return createHmac("sha256", secret).update(body).digest("hex");
}

export function verifySignature(body: string, signature: string | undefined, secret: string): boolean {
  const expected = Buffer.from(sign(body, secret), "hex");
  const given = Buffer.from(signature ?? "", "hex");
  return given.length === expected.length && timingSafeEqual(given, expected);
}
