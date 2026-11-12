import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOneEdited = scenario(
  "Add a task; the trace has a blank line 2, so verify reports its answer, a rejection, at line 3",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);

export const addOneUnanswered = scenario(
  "Add a task; the snapshot has a blank line 2, so verify reports the answer that the trace lacks at snapshot line 3",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
