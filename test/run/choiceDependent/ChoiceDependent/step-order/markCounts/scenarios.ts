import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./markCounts.ts";

export const addOne = scenario(
  "Add a task; markB counts the marks, and markA adds one, so the count depends on which of the two the queue takes first, and test reports stepOrder",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
