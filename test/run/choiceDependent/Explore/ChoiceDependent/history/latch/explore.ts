import { domain, explore } from "@natsuzora-dev/tazuna";
import { go } from "./latch.ts";

export const latchExplore = explore({ service: "latch", depth: 2, domains: [domain(go.input.ks, [["next", "stop"]])] });
