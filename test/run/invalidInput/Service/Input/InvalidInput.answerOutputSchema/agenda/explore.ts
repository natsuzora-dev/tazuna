import { domain, explore, instant } from "@natsuzora-dev/tazuna";

export const agendaExplore = explore({ service: "agenda", depth: 2, domains: [domain(instant, [])] });
