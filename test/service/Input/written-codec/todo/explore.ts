import { domain, explore } from "@natsuzora-dev/tazuna";
import { priceItem } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(priceItem.input.item, ["milk"]), domain(priceItem.input.cents, [250])],
});
