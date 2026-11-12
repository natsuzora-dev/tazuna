import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTasks } from "./todo.ts";

export const twoCopies = scenario(
  "Add two tasks at once; notifier runs the copies of task-1 and task-2 in one addTasks and requests a notification in each copy. The two requests do not depend on each other, so verify treats as matching an implementation trace that sends the request of the copy of task-2 first; no violation",
  [at("2026-10-25T10:00:00+09:00"), send(addTasks, { taskIds: ["task-1", "task-2"] })],
);
