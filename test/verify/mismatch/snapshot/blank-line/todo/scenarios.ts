import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOneEdited = scenario(
  "Add a task; the snapshot has a blank line 2, so test reports its taskAdded line, which says Buy eggs, at line 4",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
