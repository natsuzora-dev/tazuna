import { createShop } from "../src/server/app.ts";
import { LoggingMailer } from "../src/server/fakes/mailer.ts";
import { inventoryService, openInventoryDb } from "../src/server/inventory/index.ts";
import { openOrdersDb, ordersService } from "../src/server/orders/index.ts";
import { openPaymentsDb, type PaymentGateway, paymentsService } from "../src/server/payments/index.ts";
import type { Clock } from "../src/server/platform/clock.ts";
import { Recorder, recordGateway, recordMailer, recordService } from "./recorder.ts";

export const webhookSecret = "trace-webhook-secret";

const noGateway: PaymentGateway = { createCharge: async () => {}, createRefund: async () => {} };

/** The shop, or some of its services, on in-memory databases, with one recorder per service. */
export function recordedShop({
  names,
  clock,
  gateway = noGateway,
}: {
  names: readonly string[];
  clock: Clock;
  gateway?: PaymentGateway;
}) {
  const recorders = new Map(names.map((name) => [name, new Recorder(name, clock)]));
  const recorder = (name: string) => recorders.get(name) as Recorder;
  const build = {
    orders: () =>
      ordersService({
        db: openOrdersDb(),
        clock,
        mailer: recordMailer(new LoggingMailer(() => {}), recorder("orders")),
      }),
    inventory: () => inventoryService({ db: openInventoryDb(), clock }),
    payments: () =>
      paymentsService({
        db: openPaymentsDb(),
        clock,
        gateway: recordGateway(gateway, recorder("payments")),
        webhookSecret,
      }),
  } as const;
  const services = names.map((name) => recordService(build[name as keyof typeof build](), recorder(name)));
  const shop = createShop({ services, clock, sessionSecret: "trace-session-secret" });
  return { shop, services, recorders };
}
