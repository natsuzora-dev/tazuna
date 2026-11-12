import { implement } from "@orpc/server";
import { getRequest } from "@tanstack/react-start/server";
import { todoRouter as real } from "../../src/todo/todo.router.ts";
import { hold } from "./held.ts";

const os = implement(real);

export const todoRouter = {
  addTask: os.addTask.handler(({ input }) => hold("addTask", input, getRequest())),
  completeTask: os.completeTask.handler(({ input }) => hold("completeTask", input, getRequest())),
  reopenTask: os.reopenTask.handler(({ input }) => hold("reopenTask", input, getRequest())),
  renameTask: os.renameTask.handler(({ input }) => hold("renameTask", input, getRequest())),
  deleteTask: os.deleteTask.handler(({ input }) => hold("deleteTask", input, getRequest())),
  changeDue: os.changeDue.handler(({ input }) => hold("changeDue", input, getRequest())),
  changeReminders: os.changeReminders.handler(({ input }) => hold("changeReminders", input, getRequest())),
  tasks: os.tasks.handler(({ input }) => hold("tasks", input, getRequest())),
  taskDetail: os.taskDetail.handler(({ input }) => hold("taskDetail", input, getRequest())),
  reminderSettings: os.reminderSettings.handler(({ input }) => hold("reminderSettings", input, getRequest())),
  todoEvents: os.todoEvents.handler(({ input }) => hold("todoEvents", input, getRequest())),
};
