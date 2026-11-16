import { at, ref, send } from "@natsuzora-dev/tazuna";
import { addTask, changeDue, changeReminders, completeTask, deleteTask, renameTask, reopenTask } from "./commands.ts";
import { contract, Task, todoConstants } from "./data.ts";
import { taskAdded, taskCompleted, taskDeleted, taskReopened } from "./events.ts";
import { reminderSettings, taskDetail, tasks } from "./queries.ts";

const milkDueTomorrow = [
  at("2026-10-25T08:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  send(changeDue, { taskId: "task-1", dueAt: "2026-10-26T18:00:00+09:00" }),
] as const;

export const todo = contract({
  TaskId: ref(Task),
  TaskTitle: Task.fields.title,
  todoConstants,
  addTask,
  completeTask,
  reopenTask,
  renameTask,
  deleteTask,
  changeDue,
  changeReminders,
  tasks,
  taskDetail,
  reminderSettings,
  taskAdded,
  taskCompleted,
  taskReopened,
  taskDeleted,
  states: {
    milkDueTomorrow,
    milkAndCompletedEggs: [
      ...milkDueTomorrow,
      send(addTask, { taskId: "task-2", title: "Buy eggs" }),
      at("2026-10-25T09:00:00+09:00"),
      send(completeTask, { taskId: "task-2" }),
    ],
  },
});
