import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task, titledCount } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(Task.fields.title, []), domain(titledCount.input.title, [])],
});
