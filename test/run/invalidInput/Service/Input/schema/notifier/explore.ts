import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { announce } from "./notifier.ts";

export const notifierExplore = explore({
  service: "notifier",
  depth: 2,
  domains: [
    domain(announce.input.taskId, ["fulfilled"]),
    domain(todo.taskAdded.payload.taskId, ["task-1"]),
    domain(todo.taskAdded.payload.title, ["Buy milk"]),
  ],
});
