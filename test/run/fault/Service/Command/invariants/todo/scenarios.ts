import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addBlank = scenario("Add a task with a blank title; the requires titleNotBlank rejects it; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: " " }),
]);

export const addSameTitle = scenario(
  "Add two tasks with the same title; the requires newTitle rejects the second; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-2", title: "Buy milk" }),
  ],
);
