import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask, reportCount } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1"]),
    domain(reportCount.input.count, [0]),
    domain(reportCount.input.lastTaskId, ["task-1"]),
  ],
});
