import { ref } from "@natsuzora-dev/tazuna";
import { addTask, changeDue, changeReminders, completeTask, deleteTask, renameTask, reopenTask } from "./commands.ts";
import { contract, Task, todoConstants } from "./data.ts";
import { taskAdded, taskCompleted, taskDeleted, taskReopened } from "./events.ts";
import { reminderSettings, taskDetail, tasks } from "./queries.ts";

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
});
