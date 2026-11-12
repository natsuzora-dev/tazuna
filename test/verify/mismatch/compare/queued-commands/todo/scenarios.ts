import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addTwice = scenario(
  "Add two tasks; the three commands that logAdded, countAdded, and scheduleAdded send do not cause one another, so verify treats as matching an implementation trace that sends the three events of the first addTask in reverse order; no violation",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" }), send(addTask, { taskId: "task-2" })],
);
