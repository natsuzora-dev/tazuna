import { domain, explore } from "@natsuzora-dev/tazuna";
import { listScreen } from "./screens.ts";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [domain(listScreen.controls.pick.payload.taskId, ["a"])],
});
