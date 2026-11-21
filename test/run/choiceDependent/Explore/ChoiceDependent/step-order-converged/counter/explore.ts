import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask, mark } from "./counter.ts";

export const counterExplore = explore({
  service: "counter",
  depth: 2,
  domains: [domain(addTask.input.taskId, ["task-1"]), domain(mark.input.id, ["task-1"])],
});
