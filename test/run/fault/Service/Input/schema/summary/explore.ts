import { domain, explore } from "@natsuzora-dev/tazuna";
import { itemCount } from "./summary.ts";

export const summaryExplore = explore({
  service: "summary",
  depth: 2,
  domains: [domain(itemCount.input.owner, ["me"])],
});
