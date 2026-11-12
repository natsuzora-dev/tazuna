import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario(
  "Add a task; addTask emits taskAdded with an empty title, which the payload schema rejects, so test reports emittedPayloadSchema",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
