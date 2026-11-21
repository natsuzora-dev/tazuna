import { datetime, domain, explore } from "@natsuzora-dev/tazuna";
import { addTasks, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(addTasks.input.taskIds, [["task-1", "task-2"]]),
    domain(Task.fields.id, ["task-1"]),
    domain(datetime, ["2026-10-25T00:00:00Z"]),
  ],
});
