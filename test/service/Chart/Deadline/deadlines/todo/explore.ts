import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, followUp } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1"]),
    domain(completeTask.input.taskId, ["task-1"]),
    domain(followUp.input.by, ["task-1"]),
  ],
});
