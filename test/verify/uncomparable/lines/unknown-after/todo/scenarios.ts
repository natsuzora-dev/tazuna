import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario(
  "Add a task; the snapshot's after names earlier lines of the same window; no violation",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);

export const addOneUnknownAfter = scenario(
  "Add a task; in the snapshot, taskAdded's after names the later taskCountChanged#1 and taskCountChanged's after names taskAdded#9, which no line has, so verify reports unknownAfter",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
