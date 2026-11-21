import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTasks, Task } from "./greeter.ts";

export const greeterExplore = explore({
  service: "greeter",
  depth: 2,
  domains: [domain(addTasks.input.taskIds, [["task-1", "task-2"]]), domain(Task.fields.id, ["task-1"])],
});
