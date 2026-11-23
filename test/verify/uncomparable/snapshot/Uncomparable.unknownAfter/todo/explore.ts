import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";
import { Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(Task.fields.title, ["Buy milk"]),
    domain(instant, [parseInstant("2026-10-25T00:00:00Z")]),
  ],
});
