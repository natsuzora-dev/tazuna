import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario(
  "Add a task; sequencedTracker assigns status one microstep later in the second region and fixes the order, but tracker assigns it in both regions in one microstep, so test reports bothAssign",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
