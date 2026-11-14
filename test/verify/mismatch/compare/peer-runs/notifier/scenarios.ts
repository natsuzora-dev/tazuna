import { at, elsewhere, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const announcesAdded = scenario(
  "Receive taskAdded for the task that another caller adds; todo's trace of the derived run emits taskAdded for another task, so verify reports a Mismatch in it",
  [
    at("2026-10-25T10:00:00+09:00"),
    elsewhere(todo, send(todo.addTask, { taskId: "task-1", title: "Buy milk" })),
    receive(todo.taskAdded, { taskId: "task-1" }),
  ],
);
