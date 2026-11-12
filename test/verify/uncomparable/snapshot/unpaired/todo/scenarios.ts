import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario("Add a task; the run matches the snapshot; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
]);

export const addOneUnsnapshotted = scenario(
  "Add a task; the scenario has no snapshot, so test reports missingSnapshot",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
