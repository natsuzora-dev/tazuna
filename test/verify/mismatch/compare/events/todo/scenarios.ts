import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addThree = scenario("Add two tasks and a task with the first id; no violation", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  send(addTask, { taskId: "task-2", title: "Buy eggs" }),
  send(addTask, { taskId: "task-1", title: "Buy tea" }),
]);

export const addThreeWrongEvents = scenario(
  "Same inputs as addThree; the implementation trace of this scenario emits taskAdded with another title, misses the second taskAdded, and emits an extra one, so verify reports Mismatch.event, missingLine, and unexpectedLine",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    send(addTask, { taskId: "task-1", title: "Buy tea" }),
  ],
);
