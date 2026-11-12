import { at, receive, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const redelivered = scenario(
  "Receive todo.taskAdded twice with the id e1; notifier does not process the second",
  [
    at("2026-10-25T09:00:00+09:00"),
    receive(todo.taskAdded, { taskId: "task-1" }, { id: "e1" }),
    receive(todo.taskAdded, { taskId: "task-1" }, { id: "e1" }),
  ],
);
