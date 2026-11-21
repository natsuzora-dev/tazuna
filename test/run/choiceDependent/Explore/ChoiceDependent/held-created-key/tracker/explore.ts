import { domain, explore } from "@natsuzora-dev/tazuna";
import { add } from "./tracker.ts";

export const trackerExplore = explore({
  service: "tracker",
  depth: 2,
  domains: [domain(add.input.id, ["a"]), domain(add.input.text, ["a"])],
});
