import { domain, explore } from "@natsuzora-dev/tazuna";
import { itemCount } from "./summary.ts";

export const extraOutputSummaryExplore = explore({
  service: "extraOutputSummary",
  depth: 2,
  domains: [domain(itemCount.input.owner, ["me"])],
});
