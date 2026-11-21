import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { taskListScreen } from "./screens.ts";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [
    domain(todo.tasksNamed.output.titles, [[]]),
    domain(taskListScreen.controls.filter.payload.prefix, ["Buy"]),
  ],
});
