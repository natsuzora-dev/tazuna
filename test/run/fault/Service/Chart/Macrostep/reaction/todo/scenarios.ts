import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addUntitled = scenario(
  "Add a task without a title; the guard titled of countTitledTask throws, so test reports exception of countTitledTask",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "" })],
);
