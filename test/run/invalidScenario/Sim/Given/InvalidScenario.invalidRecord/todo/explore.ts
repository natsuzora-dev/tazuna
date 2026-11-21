import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-2"]), domain(Task.fields.title, ["Buy milk"])],
});
