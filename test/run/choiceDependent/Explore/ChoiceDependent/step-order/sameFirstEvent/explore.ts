import { domain, explore } from "@natsuzora-dev/tazuna";
import { set } from "./sameFirstEvent.ts";

export const sameFirstEventExplore = explore({
  service: "sameFirstEvent",
  depth: 2,
  domains: [domain(set.input.seen, [0, 1])],
});
