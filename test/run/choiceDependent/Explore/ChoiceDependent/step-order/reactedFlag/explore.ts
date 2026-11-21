import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTasks, set } from "./reactedFlag.ts";

export const reactedFlagExplore = explore({
  service: "reactedFlag",
  depth: 2,
  domains: [domain(addTasks.input.taskIds, [["task-1", "task-2"], []]), domain(set.input.by, ["task-1", "task-2"])],
});
