import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const alwaysAfterAllTransitions = scenario(
  "Add a task; on taskAdded, reminder takes both the transition from idle to checking in reminding and the transition that increments count in counting, and then evaluates the always of checking. The always reads count as 1, so reminder notifies afterCount",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
