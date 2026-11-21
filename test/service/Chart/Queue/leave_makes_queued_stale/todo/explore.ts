import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask, log, note } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1"]),
    domain(log.input.taskId, ["task-1"]),
    domain(note.input.taskId, ["task-1"]),
  ],
});
