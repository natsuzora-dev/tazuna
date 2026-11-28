import { sign, signatureHeader, type WebhookEvent } from "../payments/index.ts";

/** Posts a gateway event to the shop's webhook, signed the way the gateway signs it. */
export async function postWebhook(
  app: { request(path: string, init: RequestInit): Response | Promise<Response> },
  event: WebhookEvent,
  secret: string,
): Promise<Response> {
  const body = JSON.stringify(event);
  return app.request("/api/payments/webhooks/paygate", {
    method: "POST",
    headers: { "content-type": "application/json", [signatureHeader]: sign(body, secret) },
    body,
  });
}
