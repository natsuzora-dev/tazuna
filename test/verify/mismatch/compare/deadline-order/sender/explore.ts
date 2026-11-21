import { domain, explore } from "@natsuzora-dev/tazuna";
import { ping, pong } from "./sender.ts";

export const senderExplore = explore({
  service: "sender",
  depth: 2,
  domains: [domain(ping.input.by, ["a"]), domain(pong.input.by, ["a"])],
});
