import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { rowScreen } from "./rowScreen.ts";

export const rowsExplore = explore({
  service: "rows",
  depth: 2,
  domains: [
    domain(todo.openTasks.output.taskIds, [["task-1", "task-2"]]),
    domain(rowScreen.controls.complete.payload.taskId, ["task-1"]),
  ],
});
