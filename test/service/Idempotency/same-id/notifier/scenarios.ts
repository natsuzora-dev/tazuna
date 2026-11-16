import { at, elsewhere, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const redelivered = scenario(
  "Receive todo.taskAdded twice with the id e1; notifier does not process the second",
  [
    at("2026-10-25T09:00:00+09:00"),
    elsewhere(todo, send(todo.addTask, { taskId: "task-1", title: "Buy milk" })),
    receive(todo.taskAdded, { taskId: "task-1" }, { id: "e1" }),
    receive(todo.taskAdded, { taskId: "task-1" }, { id: "e1" }),
  ],
);
