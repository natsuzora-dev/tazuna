import { accepted, external } from "@natsuzora-dev/tazuna";
import { payments } from "../payments/contract.ts";
import { cancelOrder, placeOrder, scenario } from "./shop.ts";

export const refundCreatedCharge = scenario({
  description:
    "Place an order, accept the charge, cancel the order, and accept the refund; shop answers placeOrder and cancelOrder with acceptances without output. payments answers createCharge with an acceptance whose output holds the id of the created charge, checkout writes the chargeId of the output to its context on onAccepted, and when the order is canceled it sends refundCharge with that chargeId",
  given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: [external(payments)] },
  when: (w) => {
    const place = w.client.send(placeOrder, { amount: 1200 });
    const charge = place.request(payments.createCharge);
    w.net.deliver(charge);
    w.net.deliver(w.peer.payments.answer(charge, { result: "accepted", output: { chargeId: "ch_1" } }));
    const cancel = w.client.send(cancelOrder, {});
    const refund = cancel.request(payments.refundCharge);
    w.net.deliver(refund);
    w.net.deliver(w.peer.payments.answer(refund, accepted));
  },
  then: () => [],
});
