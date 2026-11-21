import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask } from "./latest.ts";

export const latestExplore = explore({
  service: "latest",
  depth: 2,
  domains: [domain(addTask.input.taskId, ["task-1"])],
});
