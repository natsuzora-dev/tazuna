import { at, elsewhere, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const announcesAdded = scenario("Receive taskAdded for the task that another caller adds; no violation", [
  at("2026-10-25T10:00:00+09:00"),
  elsewhere(todo, send(todo.addTask, { taskId: "task-1", title: "Buy milk" })),
  receive(todo.taskAdded, { taskId: "task-1" }),
]);

export const announcesUnadded = scenario(
  "Receive taskAdded for a task that nobody adds; todo emits no taskAdded, so test reports unproducibleEvent",
  [at("2026-10-25T10:00:00+09:00"), receive(todo.taskAdded, { taskId: "task-1" })],
);
