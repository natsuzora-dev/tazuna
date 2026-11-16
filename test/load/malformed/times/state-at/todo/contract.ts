import { at, send } from "@natsuzora-dev/tazuna";
import { addTask, contract, taskAdded } from "./todo.ts";

export const todo = contract({
  addTask,
  taskAdded,
  states: {
    milk: [at("2026-10-25T08:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
    milkAndEggs: [
      at("2026-10-25T08:00:00"),
      send(addTask, { taskId: "task-1", title: "Buy milk" }),
      at("2026-10-25T08:01:00.0009+09:00"),
      send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    ],
  },
});
