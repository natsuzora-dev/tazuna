import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOneCut = scenario(
  "Add a task; the snapshot's answer line is cut off, so it is not JSON; test reports lineSchema and compares nothing",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
