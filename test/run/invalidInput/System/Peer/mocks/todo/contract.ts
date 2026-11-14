import { at, contract, send } from "@natsuzora-dev/tazuna";
import { addTask, taskAdded, taskTitles } from "./todo.ts";

export const todo = contract({
  addTask,
  taskAdded,
  taskTitles,
  states: { milk: [at("2026-10-25T08:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })] },
});
