import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";
import { todo } from "./contract.ts";
import { Task } from "./data.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(todo.TaskTitle, ["Buy milk"]),
    domain(instant, [parseInstant("2026-10-26T18:00:00+09:00")]),
  ],
});
