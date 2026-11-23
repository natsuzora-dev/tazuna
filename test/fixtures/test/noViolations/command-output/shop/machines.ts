import { z } from "zod";
import { payments } from "../payments/contract.ts";
import { machine, orderCancelled, orderPlaced } from "./shop.ts";

export const checkout = machine({
  description: "Create a charge when an order is placed, and refund the charge when the order is canceled",
  receives: { orderPlaced, orderCancelled },
  commands: { createCharge: payments.createCharge, refundCharge: payments.refundCharge },
  initial: "waiting",
  states: {
    waiting: {},
    charging: { held: { amount: z.int().positive() } },
    charged: { held: { chargeId: z.string() } },
    refunding: { held: { chargeId: z.string() } },
  },
}).chart({
  states: {
    waiting: { on: { orderPlaced: [{ target: "charging", with: { amount: ({ payload }) => payload.amount } }] } },
    charging: {
      sends: {
        createCharge: {
          input: ({ held }) => ({ amount: held.amount }),
          onAccepted: [{ target: "charged", with: { chargeId: ({ output }) => output.chargeId } }],
          onRejected: [{ target: "waiting" }],
        },
      },
    },
    charged: {
      on: { orderCancelled: [{ target: "refunding", with: { chargeId: ({ held }) => held.chargeId } }] },
    },
    refunding: {
      sends: {
        refundCharge: {
          input: ({ held }) => ({ chargeId: held.chargeId }),
          onAccepted: [{ target: "waiting" }],
          onRejected: [{ target: "charged", with: { chargeId: ({ held }) => held.chargeId } }],
        },
      },
    },
  },
});
