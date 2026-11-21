import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const plannerExplore = explore({
  service: "planner",
  depth: 2,
  domains: [domain(todo.taskAdded.payload.taskId, ["task-1"]), domain(todo.taskAdded.payload.title, ["Buy milk"])],
});
