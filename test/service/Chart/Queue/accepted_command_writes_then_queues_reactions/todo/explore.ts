import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task, tellCount } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(tellCount.input.count, [0])],
});
