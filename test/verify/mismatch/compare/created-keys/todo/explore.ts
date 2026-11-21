import { domain, explore } from "@natsuzora-dev/tazuna";
import { see, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(see.input.id, ["task-1"]), domain(see.input.taskId, ["task-1"])],
});
