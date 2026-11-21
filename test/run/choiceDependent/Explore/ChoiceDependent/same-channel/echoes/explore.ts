import { domain, explore } from "@natsuzora-dev/tazuna";
import { ring } from "./echoes.ts";

export const echoesExplore = explore({ service: "echoes", depth: 2, domains: [domain(ring.input.by, ["a"])] });
