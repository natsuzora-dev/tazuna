import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";

export const agendaExplore = explore({
  service: "agenda",
  depth: 2,
  domains: [domain(instant, [parseInstant("2026-10-26T00:00:00+09:00")])],
});
