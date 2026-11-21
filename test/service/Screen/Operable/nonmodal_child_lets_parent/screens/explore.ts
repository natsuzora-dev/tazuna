import { domain, explore } from "@natsuzora-dev/tazuna";
import { panel } from "./screens.ts";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [domain(panel.controls.bump.payload.row, ["b"])],
});
