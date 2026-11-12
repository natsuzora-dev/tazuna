import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario(
  "Add a task; the implementation trace keeps the snapshot's order and times; no violation",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);

export const addOneReordered = scenario(
  "Add a task; the implementation trace sends taskCountChanged before taskAdded and the query 5 seconds late, so verify reports lineOrder and Mismatch.time",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
