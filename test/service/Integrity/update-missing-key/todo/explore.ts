import { domain, explore } from "@natsuzora-dev/tazuna";
import { renameTask } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(renameTask.input.taskId, ["task-1"]), domain(renameTask.input.title, ["Buy milk"])],
});
