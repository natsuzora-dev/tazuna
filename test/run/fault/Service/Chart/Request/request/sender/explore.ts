import { domain, explore } from "@natsuzora-dev/tazuna";
import { greet } from "./sender.ts";

export const senderExplore = explore({ service: "sender", depth: 2, domains: [domain(greet.input.name, ["a"])] });
