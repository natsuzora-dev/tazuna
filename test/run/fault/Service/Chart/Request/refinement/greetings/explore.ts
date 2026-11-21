import { domain, explore } from "@natsuzora-dev/tazuna";
import { greet } from "./greetings.ts";

export const greetingsExplore = explore({ service: "greetings", depth: 2, domains: [domain(greet.input.name, ["a"])] });
