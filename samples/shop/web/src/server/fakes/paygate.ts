import type { PaymentGateway, WebhookEvent } from "../payments/index.ts";

type Request =
  | { kind: "charge"; reference: string; orderId: string; amount: number }
  | { kind: "refund"; reference: string; transaction: string; amount: number };

export type Outcome = "approve" | "decline";

/**
 * Stands in for the payment gateway, which this sample has no account with. It keeps each request until `settle`
 * answers it through the webhook, or answers at once when `autoSettle` names an outcome.
 */
export class SimulatedPaygate implements PaymentGateway {
  readonly requests: Request[] = [];
  autoSettle: Outcome | undefined;
  readonly #deliver: (event: WebhookEvent) => Promise<void>;
  #transactions = 0;

  constructor(deliver: (event: WebhookEvent) => Promise<void>, autoSettle?: Outcome) {
    this.#deliver = deliver;
    this.autoSettle = autoSettle;
  }

  async createCharge(request: { reference: string; orderId: string; amount: number }) {
    this.#received({ kind: "charge", ...request });
  }

  async createRefund(request: { reference: string; transaction: string; amount: number }) {
    this.#received({ kind: "refund", ...request });
  }

  /** Answers the oldest unanswered request. */
  async settle(outcome: Outcome): Promise<void> {
    const request = this.requests.shift();
    if (request) await this.#deliver(this.#answer(request, outcome));
  }

  #received(request: Request) {
    this.requests.push(request);
    const outcome = this.autoSettle;
    // The real gateway answers later, never inside the request, so the answer waits for the next turn.
    if (outcome) setImmediate(() => void this.settle(outcome));
  }

  #answer(request: Request, outcome: Outcome): WebhookEvent {
    const { reference } = request;
    if (request.kind === "charge") {
      return outcome === "approve"
        ? { type: "charge.succeeded", reference, transaction: `txn_${++this.#transactions}` }
        : { type: "charge.failed", reference, failureCode: "card_declined" };
    }
    return outcome === "approve"
      ? { type: "refund.succeeded", reference }
      : { type: "refund.failed", reference, failureCode: "refund_window_closed" };
  }
}
