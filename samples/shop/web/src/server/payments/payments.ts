import { eq, or } from "drizzle-orm";
import type { Clock } from "../platform/clock.ts";
import { openDatabase } from "../platform/db.ts";
import { publish } from "../platform/outbox.ts";
import type { PaymentGateway, WebhookEvent } from "./gateway.ts";
import * as schema from "./schema.ts";
import { payments } from "./schema.ts";

/** The events payments publishes. */
export type PaymentsEvent =
  | { type: "payment.charge_started"; data: { orderId: string; amount: number } }
  | { type: "payment.captured"; data: { orderId: string; transaction: string } }
  | { type: "payment.declined"; data: { orderId: string } }
  | { type: "payment.refund_started"; data: { orderId: string; transaction: string; amount: number } }
  | { type: "payment.refunded"; data: { orderId: string } }
  | { type: "payment.refund_failed"; data: { orderId: string } };

export function openPaymentsDb(file = ":memory:") {
  return openDatabase(file, schema, `${import.meta.dirname}/migrations`);
}

export type PaymentsDb = ReturnType<typeof openPaymentsDb>;
type Tx = Parameters<Parameters<PaymentsDb["transaction"]>[0]>[0];
type Payment = typeof payments.$inferSelect;
type GatewayCall = () => Promise<void>;

export function createPayments({ db, clock, gateway }: { db: PaymentsDb; clock: Clock; gateway: PaymentGateway }) {
  const emit = (tx: Tx, event: PaymentsEvent) => publish(tx, event, clock.now());
  const set = (tx: Tx, orderId: string, change: Partial<Payment>) =>
    tx.update(payments).set(change).where(eq(payments.orderId, orderId)).run();

  /** Calls the gateway after the transaction commits, so the call never reports a change that rolled back. */
  function afterCommit(work: (tx: Tx) => GatewayCall | undefined) {
    const call = db.transaction(work);
    call?.().catch((error) => console.error("payment gateway call failed", error));
  }

  /** Refunds a captured charge once its order is cancelled, whichever of the two came first. */
  function refundIfCancelled(tx: Tx, payment: Payment): GatewayCall | undefined {
    if (payment.status !== "captured" || !payment.orderCancelled || payment.transactionId === null) return;
    const { orderId, amountCents: amount, transactionId: transaction } = payment;
    const reference = `refund-${orderId}`;
    set(tx, orderId, { status: "refunding", refundReference: reference });
    emit(tx, { type: "payment.refund_started", data: { orderId, transaction, amount } });
    return () => gateway.createRefund({ reference, transaction, amount });
  }

  return {
    get: (orderId: string) => db.select().from(payments).where(eq(payments.orderId, orderId)).get(),

    /** Charges an order once. Orders never asks for nothing; if it did, its payment deadline cancels the order. */
    charge(orderId: string, amount: number) {
      afterCommit((tx) => {
        if (amount <= 0 || tx.select().from(payments).where(eq(payments.orderId, orderId)).get()) return;
        const reference = `charge-${orderId}`;
        tx.insert(payments)
          .values({
            orderId,
            amountCents: amount,
            status: "charging",
            chargeReference: reference,
            createdAt: clock.now(),
          })
          .run();
        emit(tx, { type: "payment.charge_started", data: { orderId, amount } });
        return () => gateway.createCharge({ reference, orderId, amount });
      });
    },

    orderCancelled(orderId: string) {
      afterCommit((tx) => {
        const payment = tx.select().from(payments).where(eq(payments.orderId, orderId)).get();
        if (!payment) return;
        set(tx, orderId, { orderCancelled: true });
        return refundIfCancelled(tx, { ...payment, orderCancelled: true });
      });
    },

    /** Applies the gateway's report on a charge or refund. Returns false when no payment has the reference. */
    gatewayReported(event: WebhookEvent): boolean {
      let found = true;
      afterCommit((tx) => {
        const payment = tx
          .select()
          .from(payments)
          .where(or(eq(payments.chargeReference, event.reference), eq(payments.refundReference, event.reference)))
          .get();
        if (!payment) {
          found = false;
          return;
        }
        const { orderId } = payment;
        switch (event.type) {
          case "charge.succeeded": {
            const { transaction } = event;
            set(tx, orderId, { status: "captured", transactionId: transaction });
            emit(tx, { type: "payment.captured", data: { orderId, transaction } });
            return refundIfCancelled(tx, { ...payment, status: "captured", transactionId: transaction });
          }
          case "charge.failed":
            set(tx, orderId, { status: "declined" });
            emit(tx, { type: "payment.declined", data: { orderId } });
            return;
          case "refund.succeeded":
            set(tx, orderId, { status: "refunded" });
            emit(tx, { type: "payment.refunded", data: { orderId } });
            return;
          case "refund.failed":
            if (payment.status === "refunding") set(tx, orderId, { status: "refund_refused" });
            emit(tx, { type: "payment.refund_failed", data: { orderId } });
            return;
        }
      });
      return found;
    },
  };
}

export type Payments = ReturnType<typeof createPayments>;
