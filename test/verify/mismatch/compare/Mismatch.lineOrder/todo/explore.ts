import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask, count, log, schedule } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1"]),
    domain(count.input.taskId, ["task-1"]),
    domain(log.input.taskId, ["task-1"]),
    domain(schedule.input.taskId, ["task-1"]),
  ],
});
