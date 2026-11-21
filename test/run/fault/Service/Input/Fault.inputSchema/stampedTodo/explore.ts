import { datetime, domain, explore } from "@natsuzora-dev/tazuna";
import { addTask, setReminder } from "./todo.ts";

export const stampedTodoExplore = explore({
  service: "stampedTodo",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1"]),
    domain(setReminder.input.taskId, ["task-1"]),
    domain(datetime, ["2026-10-25T00:00:00Z"]),
  ],
});
