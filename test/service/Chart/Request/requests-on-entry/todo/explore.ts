import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";
import { addDoneTask, addTask, completeTask } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1"]),
    domain(completeTask.input.taskId, ["task-1"]),
    domain(instant, [parseInstant("2026-10-25T00:00:00Z")]),
    domain(addDoneTask.input.taskId, ["task-1"]),
  ],
});
