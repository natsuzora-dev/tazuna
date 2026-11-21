import { domain, explore } from "@natsuzora-dev/tazuna";
import { go, touch } from "./door.ts";

export const doorExplore = explore({
  service: "door",
  depth: 2,
  domains: [domain(go.input.ks, [["open", "close"]]), domain(touch.input.by, [["a", "b"]])],
});
