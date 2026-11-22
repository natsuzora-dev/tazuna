import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, setReminder } from "./todo.ts";

export const stampedTodoExplore = explore({
  service: "stampedTodo",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1"]),
    domain(setReminder.input.taskId, ["task-1"]),
    domain(instant, [parseInstant("2026-10-25T00:00:00Z")]),
  ],
});
