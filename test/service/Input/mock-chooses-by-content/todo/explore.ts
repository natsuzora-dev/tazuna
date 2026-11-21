import { datetime, domain, explore } from "@natsuzora-dev/tazuna";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(datetime, ["2026-10-26T00:00:00+09:00"])],
});
