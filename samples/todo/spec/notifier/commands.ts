import { emit } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";
import { command, NotificationPermission } from "./data.ts";
import { notificationPermissionRecorded, openTaskForgotten, openTaskRecorded, tooManyWarned } from "./events.ts";

export const warn = command({
  input: { count: z.number() },
  emits: [tooManyWarned],
}).decide(({ input }) => [emit(tooManyWarned, { count: input.count })]);

export const recordOpenTask = command({
  input: { taskId: todo.TaskId },
  emits: [openTaskRecorded],
}).decide(({ input, records }) =>
  records.OpenTask.get(input.taskId) === undefined ? [emit(openTaskRecorded, { taskId: input.taskId })] : [],
);

export const forgetOpenTask = command({
  input: { taskId: todo.TaskId },
  emits: [openTaskForgotten],
}).decide(({ input, records }) =>
  records.OpenTask.get(input.taskId) === undefined ? [] : [emit(openTaskForgotten, { taskId: input.taskId })],
);

export const recordNotificationPermission = command({
  input: { status: NotificationPermission.fields.status.unwrap().exclude(["undetermined"]) },
  emits: [notificationPermissionRecorded],
}).decide(({ input }) => [emit(notificationPermissionRecorded, { status: input.status })]);
