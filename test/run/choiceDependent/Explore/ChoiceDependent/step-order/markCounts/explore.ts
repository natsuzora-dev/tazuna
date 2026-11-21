import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask, markA, markB } from "./markCounts.ts";

export const markCountsExplore = explore({
  service: "markCounts",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1", "task-2"]),
    domain(markA.input.id, ["task-1", "task-2"]),
    domain(markB.input.id, ["task-1", "task-2"]),
  ],
});
