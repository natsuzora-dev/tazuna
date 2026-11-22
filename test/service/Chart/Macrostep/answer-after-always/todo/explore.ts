import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(addTask.input.taskId, ["task-1"]), domain(instant, [parseInstant("2026-10-26T00:00:00+09:00")])],
});
