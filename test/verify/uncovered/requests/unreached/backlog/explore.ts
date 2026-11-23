import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task, taskTitles } from "./backlog.ts";

export const backlogExplore = explore({
  service: "backlog",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1", "task-2"]),
    domain(Task.fields.title, ["Buy milk", "task-1"]),
    domain(taskTitles.input.prefix, ["task-1", "Buy milk"]),
  ],
});
