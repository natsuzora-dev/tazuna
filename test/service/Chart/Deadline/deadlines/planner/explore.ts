import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask } from "./planner.ts";

export const plannerExplore = explore({
  service: "planner",
  depth: 2,
  domains: [domain(addTask.input.taskId, ["task-1"])],
});
