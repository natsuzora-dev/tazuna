import { at, ref, send } from "@natsuzora-dev/tazuna";
import { addTask, contract, Task, taskAdded } from "./todo.ts";

export const todo = contract({
  TaskId: ref(Task),
  taskAdded,
  addTask,
  states: { milk: [at("2026-10-25T08:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })] },
});
