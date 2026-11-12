import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTasks } from "./claims.ts";

export const addTwo = scenario(
  "Add task-1 and task-2; the copies of claimer for the two tasks send claim, and the one taken last decides the winner, so test reports stepOrder",
  [at("2026-10-25T09:00:00+09:00"), send(addTasks, { taskIds: ["task-1", "task-2"] })],
);
