import { z } from "zod";
import { payments } from "../payments/contract.ts";
import { machine, orderCancelled, orderPlaced } from "./shop.ts";

export const checkout = machine({
  description: "Create a charge when an order is placed, and refund the charge when the order is canceled",
  context: {
    amount: z.number().int().positive().nullable().default(null),
    chargeId: z.string().nullable().default(null),
  },
  receives: { orderPlaced, orderCancelled },
  commands: { createCharge: payments.createCharge, refundCharge: payments.refundCharge },
  initial: "waiting",
  states: {
    waiting: {},
    charging: { held: { amount: z.number().int().positive() } },
    charged: { held: { chargeId: z.string() } },
    refunding: { held: { chargeId: z.string() } },
  },
}).chart({
  states: {
    waiting: { on: { orderPlaced: [{ target: "charging", assign: { amount: ({ payload }) => payload.amount } }] } },
    charging: {
      holds: { amount: ({ context }) => context.amount },
      sends: {
        createCharge: {
          input: ({ held }) => ({ amount: held.amount }),
          onAccepted: [{ target: "charged", assign: { chargeId: ({ output }) => output.chargeId } }],
          onRejected: [{ target: "waiting" }],
        },
      },
    },
    charged: {
      holds: { chargeId: ({ context }) => context.chargeId },
      on: { orderCancelled: [{ target: "refunding" }] },
    },
    refunding: {
      holds: { chargeId: ({ context }) => context.chargeId },
      sends: {
        refundCharge: {
          input: ({ held }) => ({ chargeId: held.chargeId }),
          onAccepted: [{ target: "waiting" }],
          onRejected: [{ target: "charged" }],
        },
      },
    },
  },
});
