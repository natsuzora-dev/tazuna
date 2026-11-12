import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario("Add a task; its snapshot and trace pair up; no violation", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
]);

export const addTwo = scenario("Add two tasks; its snapshot has no trace, so verify reports missingTrace", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  send(addTask, { taskId: "task-2", title: "Buy eggs" }),
]);
