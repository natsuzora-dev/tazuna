import { domain, explore } from "@natsuzora-dev/tazuna";
import { ring } from "./alarms.ts";

export const alarmsExplore = explore({ service: "alarms", depth: 2, domains: [domain(ring.input.by, ["a"])] });
