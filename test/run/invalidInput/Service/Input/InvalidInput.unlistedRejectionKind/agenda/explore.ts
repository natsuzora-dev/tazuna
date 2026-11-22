import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";

export const agendaExplore = explore({
  service: "agenda",
  depth: 2,
  domains: [domain(instant, [parseInstant("2026-10-25T00:00:00Z")])],
});
