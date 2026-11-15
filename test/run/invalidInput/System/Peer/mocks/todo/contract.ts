import { at, contract, ref, send } from "@natsuzora-dev/tazuna";
import { addTask, addTitle, completeTask, Task, taskAdded, tasks, taskTitles } from "./todo.ts";

export const todo = contract({
  TaskId: ref(Task),
  addTask,
  addTitle,
  completeTask,
  taskAdded,
  taskTitles,
  tasks,
  states: {
    milk: [at("2026-10-25T08:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
    milkAndBread: [
      at("2026-10-25T08:00:00+09:00"),
      send(addTitle, { title: "Buy milk" }),
      send(addTitle, { title: "Buy bread" }),
    ],
    thirtyMilks: [
      at("2026-10-25T08:00:00+09:00"),
      ...Array.from({ length: 30 }, () => send(addTitle, { title: "Buy milk" })),
    ],
  },
});
