import { datetime, domain, explore } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(addTask.input.taskId, ["task-1"]), domain(datetime, ["2026-10-26T00:00:00+09:00"])],
});
