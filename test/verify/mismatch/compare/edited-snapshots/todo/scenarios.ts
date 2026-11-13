import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOneOperated = scenario(
  "Add a task; its snapshot, edited by hand, adds an out operation line that no run writes, and the implementation trace of this scenario has another payload in it, so verify reports Mismatch.operation",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1" })],
);

export const addOneFulfilled = scenario(
  "Add a task; its snapshot, edited by hand, answers addTask with a fulfilled result that no run writes, and the implementation trace of this scenario answers with another output, so verify reports Mismatch.output",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1" })],
);
