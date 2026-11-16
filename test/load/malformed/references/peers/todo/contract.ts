import { at, send } from "@natsuzora-dev/tazuna";
import { addTask, contract, taskAdded } from "./todo.ts";

export const todo = contract({
  addTask,
  taskAdded,
  states: { milk: [at("2026-10-25T08:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })] },
});
