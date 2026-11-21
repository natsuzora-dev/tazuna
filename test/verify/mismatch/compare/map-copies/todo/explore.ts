import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTasks } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(addTasks.input.taskIds, [["task-1", "task-2"]])],
});
