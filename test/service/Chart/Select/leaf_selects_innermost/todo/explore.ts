import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask, pickTask, remind } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["left"]),
    domain(pickTask.input.taskId, ["task-1"]),
    domain(remind.input.by, ["left"]),
  ],
});
