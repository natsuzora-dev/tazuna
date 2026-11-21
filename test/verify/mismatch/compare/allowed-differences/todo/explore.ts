import { domain, explore } from "@natsuzora-dev/tazuna";
import { taskNote } from "./queries.ts";
import { Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(taskNote.input.taskId, [""]), domain(Task.fields.id, ["task-1"])],
});
