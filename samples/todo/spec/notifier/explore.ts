import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { warn } from "./commands.ts";

export const notifierExplore = explore({
  service: "notifier",
  depth: 2,
  domains: [domain(warn.input.count, [0]), domain(todo.addTask.input.taskId, ["task-1"])],
});
