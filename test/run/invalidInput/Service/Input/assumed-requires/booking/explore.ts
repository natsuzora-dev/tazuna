import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";

export const bookingExplore = explore({
  service: "booking",
  depth: 2,
  domains: [domain(instant, [parseInstant("2026-10-26T00:00:00Z")])],
});
