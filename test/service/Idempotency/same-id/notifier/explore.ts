import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { OpenTask } from "./notifier.ts";

export const notifierExplore = explore({
  service: "notifier",
  depth: 2,
  domains: [domain(OpenTask.fields.taskId, ["accepted"]), domain(todo.taskAdded.payload.taskId, ["task-1"])],
});
