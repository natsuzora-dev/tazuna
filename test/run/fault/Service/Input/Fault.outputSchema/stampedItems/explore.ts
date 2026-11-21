import { domain, explore } from "@natsuzora-dev/tazuna";
import { itemTime } from "./items.ts";

export const stampedItemsExplore = explore({
  service: "stampedItems",
  depth: 2,
  domains: [domain(itemTime.input.itemId, ["item-1"])],
});
