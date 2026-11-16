import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./earlyFirstTodo.ts";

export const addOne = scenario(
  "Add a task and leave the deadlines to the search, which tries both orders of the tie and lists earlyDeadline first; the reminder sent depends on the order, so test reports deadlineOrder after the time that the search appends",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
