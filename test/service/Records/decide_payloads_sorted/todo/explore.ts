import { domain, explore } from "@natsuzora-dev/tazuna";
import { planTasks, shelve } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(shelve.input.names, [[]]),
    domain(shelve.input.entries, [[]]),
    domain(planTasks.input.entries, [[]]),
  ],
});
