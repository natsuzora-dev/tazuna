import { domain, explore } from "@natsuzora-dev/tazuna";
import { ring } from "./bells.ts";

export const bellsExplore = explore({ service: "bells", depth: 2, domains: [domain(ring.input.by, ["a"])] });
