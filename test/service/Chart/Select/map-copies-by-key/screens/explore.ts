import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { listScreen } from "./listScreen.ts";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [
    domain(todo.tasks.output.taskIds, [["task-1", "task-2"]]),
    domain(listScreen.controls.complete.payload.taskId, ["task-1"]),
  ],
});
