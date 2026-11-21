import { datetime, domain, explore } from "@natsuzora-dev/tazuna";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [domain(datetime, ["2026-10-25T00:00:00Z"])],
});
