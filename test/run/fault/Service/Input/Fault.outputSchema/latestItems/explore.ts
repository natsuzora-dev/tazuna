import { domain, explore } from "@natsuzora-dev/tazuna";
import { smallItems } from "./items.ts";

export const latestItemsExplore = explore({
  service: "latestItems",
  depth: 2,
  domains: [domain(smallItems.input.shelfId, ["shelf-1"])],
});
