import { domain, explore } from "@natsuzora-dev/tazuna";
import { go } from "./waiter.ts";

export const waiterExplore = explore({ service: "waiter", depth: 2, domains: [domain(go.input.ks, [["1", "2"]])] });
