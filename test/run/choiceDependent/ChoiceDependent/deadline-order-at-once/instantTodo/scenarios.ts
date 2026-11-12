import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./instantTodo.ts";

export const addOneAtOnce = scenario(
  "Add a task; the two deadlines of reminder tie at the end of addTask, lateDeadline fires first as the first in entry order, leaves waiting and cancels the other, and the reminder sent depends on which fires first, so test reports deadlineOrder",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
