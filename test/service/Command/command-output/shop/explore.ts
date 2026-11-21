import { domain, explore } from "@natsuzora-dev/tazuna";
import { payments } from "../payments/contract.ts";
import { placeOrder } from "./shop.ts";

export const shopExplore = explore({
  service: "shop",
  depth: 2,
  domains: [domain(placeOrder.input.amount, [1200]), domain(payments.createCharge.output.chargeId, ["ch_1"])],
});
