import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask } from "./pinger.ts";

export const pingerExplore = explore({
  service: "pinger",
  depth: 2,
  domains: [domain(addTask.input.taskId, ["task-1"])],
});
