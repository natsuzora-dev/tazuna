import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const separateValues = scenario(
  "Add two tasks; in the one microstep of taskAdded, the transition of counting reads and writes only count and the transition of remembering only lastTaskId, so tracker reports no pair of the two transitions. The input of the sends of reporting is evaluated after the microstep, so reading the count that counting writes makes no pair",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1" }), send(addTask, { taskId: "task-2" })],
);
