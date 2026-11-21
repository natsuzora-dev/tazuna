import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-9"]), domain(Task.fields.title, ["task-9"])],
});
