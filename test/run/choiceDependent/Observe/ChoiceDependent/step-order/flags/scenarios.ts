import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./flags.ts";

export const addOne = scenario(
  "Add a task; flagger sends raise and lower from one state, and the one taken last decides the flag, so test reports stepOrder",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
