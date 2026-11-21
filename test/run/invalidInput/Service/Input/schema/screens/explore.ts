import { domain, explore } from "@natsuzora-dev/tazuna";
import { counterScreen } from "./screens.ts";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [domain(counterScreen.controls.countSet.payload.count, [3])],
});
