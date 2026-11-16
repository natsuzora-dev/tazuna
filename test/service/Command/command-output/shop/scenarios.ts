import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { payments } from "../payments/contract.ts";
import { checkout } from "./machines.ts";
import { cancelOrder, placeOrder } from "./shop.ts";

export const refundCreatedCharge = scenario(
  "Place an order, accept the charge, cancel the order, and accept the refund; shop answers placeOrder and cancelOrder with acceptances without output. payments answers createCharge with an acceptance whose output holds the id of the created charge, checkout writes the chargeId of the output to its context on onAccepted, and when the order is canceled it sends refundCharge with that chargeId",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(placeOrder, { amount: 1200 }),
    mock(checkout, [payments.createCharge, { result: "accepted", output: { chargeId: "ch_1" } }]),
    send(cancelOrder, {}),
    mock(checkout, [payments.refundCharge, { result: "accepted" }]),
  ],
);
