import { os } from "@orpc/server";
import { todo } from "@todo/spec/todo";
import { eq } from "drizzle-orm";
import { z } from "zod";
import { changes, notifyChange } from "../changes.server.ts";
import { db } from "../db/index.server.ts";
import { settings, tasks as taskTable } from "../db/schema.ts";
import { commandErrors } from "./errors.ts";
import { events, publish } from "./events.server.ts";
import { command } from "./idempotency.server.ts";
import { readReminderSettings, readTaskDetail, readTasks } from "./queries.server.ts";
import { decideReminderTime, stopDecidingReminderTime } from "./reminders.server.ts";

const { TASK_ALREADY_EXISTS, TASK_NOT_FOUND, ALREADY_COMPLETED, NOT_COMPLETED, DUE_IN_PAST } = commandErrors;

const findTask = (taskId: string) => db.select().from(taskTable).where(eq(taskTable.id, taskId)).get();

const reminderKeptOnReopen = (remindAt: number | null) =>
  remindAt !== null && remindAt > Date.now() ? remindAt : null;

async function* answers<T>(read: () => T, signal: AbortSignal | undefined): AsyncGenerator<T> {
  const changed = changes.subscribe("changed", { signal });
  yield read();
  for await (const _ of changed) yield read();
}

export const todoRouter = {
  addTask: command
    .input(z.object(todo.addTask.input))
    .errors({ TASK_ALREADY_EXISTS })
    .handler(({ input: { taskId, title }, errors, context }) => {
      if (findTask(taskId) !== undefined) throw errors.TASK_ALREADY_EXISTS();
      db.insert(taskTable).values({ id: taskId, title, createdAt: Date.now(), reminderDecision: "pending" }).run();
      notifyChange();
      publish({ name: "taskAdded", payload: { taskId } }, context.headers);
      void decideReminderTime(taskId);
    }),

  completeTask: command
    .input(z.object(todo.completeTask.input))
    .errors({ TASK_NOT_FOUND, ALREADY_COMPLETED })
    .handler(({ input: { taskId }, errors, context }) => {
      const task = findTask(taskId);
      if (task === undefined) throw errors.TASK_NOT_FOUND();
      if (task.completedAt !== null) throw errors.ALREADY_COMPLETED();
      db.update(taskTable).set({ completedAt: Date.now() }).where(eq(taskTable.id, taskId)).run();
      notifyChange();
      publish({ name: "taskCompleted", payload: { taskId } }, context.headers);
    }),

  reopenTask: command
    .input(z.object(todo.reopenTask.input))
    .errors({ TASK_NOT_FOUND, NOT_COMPLETED })
    .handler(({ input: { taskId }, errors, context }) => {
      const task = findTask(taskId);
      if (task === undefined) throw errors.TASK_NOT_FOUND();
      if (task.completedAt === null) throw errors.NOT_COMPLETED();
      db.update(taskTable)
        .set({ completedAt: null, remindAt: reminderKeptOnReopen(task.remindAt) })
        .where(eq(taskTable.id, taskId))
        .run();
      notifyChange();
      publish({ name: "taskReopened", payload: { taskId } }, context.headers);
    }),

  renameTask: command
    .input(z.object(todo.renameTask.input))
    .errors({ TASK_NOT_FOUND })
    .handler(({ input: { taskId, title }, errors }) => {
      if (findTask(taskId) === undefined) throw errors.TASK_NOT_FOUND();
      db.update(taskTable).set({ title }).where(eq(taskTable.id, taskId)).run();
      notifyChange();
    }),

  deleteTask: command
    .input(z.object(todo.deleteTask.input))
    .errors({ TASK_NOT_FOUND })
    .handler(({ input: { taskId }, errors, context }) => {
      if (findTask(taskId) === undefined) throw errors.TASK_NOT_FOUND();
      stopDecidingReminderTime(taskId);
      db.delete(taskTable).where(eq(taskTable.id, taskId)).run();
      notifyChange();
      publish({ name: "taskDeleted", payload: { taskId } }, context.headers);
    }),

  changeDue: command
    .input(z.object(todo.changeDue.input))
    .errors({ TASK_NOT_FOUND, DUE_IN_PAST })
    .handler(({ input: { taskId, dueAt }, errors }) => {
      if (findTask(taskId) === undefined) throw errors.TASK_NOT_FOUND();
      if (dueAt !== null && dueAt <= Date.now()) throw errors.DUE_IN_PAST();
      if (dueAt === null) {
        db.update(taskTable)
          .set({ dueAt: null, remindAt: null, reminderDecision: "pending" })
          .where(eq(taskTable.id, taskId))
          .run();
        void decideReminderTime(taskId);
      } else {
        stopDecidingReminderTime(taskId);
        db.update(taskTable)
          .set({ dueAt, remindAt: dueAt, reminderDecision: "decided" })
          .where(eq(taskTable.id, taskId))
          .run();
      }
      notifyChange();
    }),

  changeReminders: command.input(z.object(todo.changeReminders.input)).handler(({ input: { shouldRemind } }) => {
    db.insert(settings)
      .values({ id: 1, shouldRemind })
      .onConflictDoUpdate({ target: settings.id, set: { shouldRemind } })
      .run();
    notifyChange();
  }),

  tasks: os.input(z.object(todo.tasks.input)).handler(({ input, signal }) => answers(() => readTasks(input), signal)),

  taskDetail: os
    .input(z.object(todo.taskDetail.input))
    .handler(({ input, signal }) => answers(() => readTaskDetail(input), signal)),

  reminderSettings: os
    .input(z.object(todo.reminderSettings.input))
    .handler(({ signal }) => answers(readReminderSettings, signal)),

  todoEvents: os.handler(({ signal }) => events.subscribe("todo", { signal })),
};
