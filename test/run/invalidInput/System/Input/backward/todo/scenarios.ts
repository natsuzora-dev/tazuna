import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addTwo = scenario("Add two tasks; no violation", [
  at("2026-10-25T10:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  at("2026-10-25T11:00:00+09:00"),
  send(addTask, { taskId: "task-2", title: "Walk" }),
]);

export const addTwoBackward = scenario(
  "Add two tasks, giving the second an at earlier than the first; test reports earlierAt",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-2", title: "Walk" }),
  ],
);
