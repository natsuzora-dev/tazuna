import { datetime, domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [
    domain(todo.TaskTitle, ["Buy milk"]),
    domain(datetime, ["2026-10-26T18:00:00+09:00"]),
    domain(todo.tasks.output.tasks, [
      [{ taskId: "task-1", title: "Buy milk", dueAt: "2026-10-26T18:00:00+09:00", completedAt: null }],
    ]),
    domain(todo.addTask.input.taskId, ["task-1"]),
  ],
});
