import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addLong = scenario(
  "Add a task with a long title; the guard short of countAddedTask keeps it from sending countAdded; no violation",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk and bread" })],
);
