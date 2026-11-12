import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario(
  "Add a task; firstTaskWatcher reads the held task, while watcher reads latest, which no state holds, so test reports unheld",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
