import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./latest.ts";

export const rememberOne = scenario(
  "Add a task; both regions of tracker assign lastTaskId in one microstep, so the result depends on their order, so test reports bothAssign",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
