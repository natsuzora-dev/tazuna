import { domain, explore } from "@natsuzora-dev/tazuna";
import { item } from "./items.ts";

export const itemsExplore = explore({ service: "items", depth: 2, domains: [domain(item.input.itemId, ["item-1"])] });
