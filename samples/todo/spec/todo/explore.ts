import { date, datetime, domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "./contract.ts";
import { Task } from "./data.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(todo.TaskTitle, ["Buy milk"]),
    domain(datetime, ["2026-10-26T18:00:00+09:00"]),
    domain(date, ["2026-10-26"]),
  ],
});
