import { domain, explore } from "@natsuzora-dev/tazuna";
import { filteredScreen, listScreen } from "./picker.ts";

export const pickerExplore = explore({
  service: "picker",
  depth: 2,
  domains: [
    domain(listScreen.controls.pick.payload.taskId, ["task-1"]),
    domain(filteredScreen.controls.pick.payload.taskId, ["task-1"]),
  ],
});
