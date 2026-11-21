import { domain, explore } from "@natsuzora-dev/tazuna";
import { go } from "./door.ts";

export const doorExplore = explore({ service: "door", depth: 2, domains: [domain(go.input.ks, [["next", "stop"]])] });
