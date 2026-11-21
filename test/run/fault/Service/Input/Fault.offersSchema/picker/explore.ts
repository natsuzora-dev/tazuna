import { domain, explore } from "@natsuzora-dev/tazuna";
import { filteredScreen } from "./picker.ts";

export const pickerExplore = explore({
  service: "picker",
  depth: 2,
  domains: [domain(filteredScreen.controls.pick.payload.taskId, ["task-1"])],
});
