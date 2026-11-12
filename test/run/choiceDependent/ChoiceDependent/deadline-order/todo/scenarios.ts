import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario(
  "Add a task and wait an hour; earlyReminder fires first as the first in entry order; no violation",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1" }), at("2026-10-25T11:00:00+09:00")],
);

export const addOnly = scenario("Add a task and leave the deadlines to `tazuna test`; no violation", [
  at("2026-10-25T10:00:00+09:00"),
  send(addTask, { taskId: "task-1" }),
]);
