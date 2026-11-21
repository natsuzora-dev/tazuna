import { domain, explore } from "@natsuzora-dev/tazuna";
import { greet } from "./sender.ts";

export const namelessSenderExplore = explore({
  service: "namelessSender",
  depth: 2,
  domains: [domain(greet.input.name, ["a"])],
});
