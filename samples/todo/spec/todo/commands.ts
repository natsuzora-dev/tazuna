import { emit, instant, ref } from "@natsuzora-dev/tazuna";
import { command, Settings, Task } from "./data.ts";
import {
  dueChanged,
  dueCleared,
  reminderDecisionFailed,
  reminderScheduled,
  remindersChanged,
  reminderTimeReached,
  reminderTimeReachedRecorded,
  taskAdded,
  taskAddedRecorded,
  taskCompleted,
  taskCompletedRecorded,
  taskDeleted,
  taskDeletedRecorded,
  taskRenamed,
  taskReopened,
  taskReopenedRecorded,
} from "./events.ts";

export const addTask = command({
  callers: ["screens"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded],
}).decide(({ input, now }) => [
  emit(taskAddedRecorded, {
    id: input.taskId,
    title: input.title,
    createdAt: now,
    completedAt: null,
    dueAt: null,
    remindAt: null,
    reminderDecision: "pending",
  }),
  emit(taskAdded, { taskId: input.taskId, at: now }),
]);

export const completeTask = command({
  callers: ["screens"],
  input: { taskId: ref(Task) },
  emits: [taskCompletedRecorded, taskCompleted],
  requires: { notCompleted: ({ refs }) => refs.taskId.completedAt === null },
  ensures: {
    completed: ({ input, records }) => records.Task.get(input.taskId)?.completedAt !== null,
  },
}).decide(({ input, now }) => [
  emit(taskCompletedRecorded, { id: input.taskId, completedAt: now }),
  emit(taskCompleted, { taskId: input.taskId, at: now }),
]);

export const reopenTask = command({
  callers: ["screens"],
  input: { taskId: ref(Task) },
  emits: [taskReopenedRecorded, taskReopened],
  requires: { completed: ({ refs }) => refs.taskId.completedAt !== null },
  ensures: { reopened: ({ input, records }) => records.Task.get(input.taskId)?.completedAt === null },
}).decide(({ input, refs, now }) => {
  const { remindAt } = refs.taskId;
  return [
    emit(taskReopenedRecorded, {
      id: input.taskId,
      completedAt: null,
      // A reminder time that passed while the task was completed is dropped, so the reopened task is not reminded.
      remindAt: remindAt !== null && remindAt > now ? remindAt : null,
    }),
    emit(taskReopened, { taskId: input.taskId, at: now }),
  ];
});

export const renameTask = command({
  callers: ["screens"],
  input: { taskId: ref(Task), title: Task.fields.title },
  emits: [taskRenamed],
}).decide(({ input }) => [emit(taskRenamed, { id: input.taskId, title: input.title })]);

export const deleteTask = command({
  callers: ["screens"],
  input: { taskId: ref(Task) },
  emits: [taskDeletedRecorded, taskDeleted],
}).decide(({ input, now }) => [
  emit(taskDeletedRecorded, { id: input.taskId }),
  emit(taskDeleted, { taskId: input.taskId, at: now }),
]);

export const changeDue = command({
  callers: ["screens"],
  input: { taskId: ref(Task), dueAt: instant.nullable() },
  emits: [dueChanged, dueCleared],
  requires: {
    notPast: ({ input, now }) => input.dueAt === null || input.dueAt > now,
  },
}).decide(({ input }) => [
  // Clearing the due date leaves the reminder to businessDayReminder, as for a task added without one.
  input.dueAt === null
    ? emit(dueCleared, { id: input.taskId, dueAt: null, remindAt: null, reminderDecision: "pending" })
    : emit(dueChanged, { id: input.taskId, dueAt: input.dueAt, remindAt: input.dueAt, reminderDecision: "decided" }),
]);

export const changeReminders = command({
  callers: ["screens"],
  input: { shouldRemind: Settings.fields.shouldRemind.unwrap() },
  emits: [remindersChanged],
}).decide(({ input }) => [emit(remindersChanged, { shouldRemind: input.shouldRemind })]);

export const setReminder = command({
  callers: ["todo"],
  input: { taskId: ref(Task), remindAt: instant },
  emits: [reminderScheduled],
}).decide(({ input }) => [
  emit(reminderScheduled, { id: input.taskId, remindAt: input.remindAt, reminderDecision: "decided" }),
]);

export const recordReminderDecisionFailed = command({
  callers: ["todo"],
  input: { taskId: ref(Task) },
  emits: [reminderDecisionFailed],
}).decide(({ input }) => [emit(reminderDecisionFailed, { id: input.taskId, reminderDecision: "failed" })]);

export const recordReminderTimeReached = command({
  callers: ["todo"],
  input: { taskId: ref(Task) },
  emits: [reminderTimeReachedRecorded, reminderTimeReached],
}).decide(({ refs }) => [
  emit(reminderTimeReachedRecorded, { id: refs.taskId.id, remindAt: null }),
  emit(reminderTimeReached, { title: refs.taskId.title }),
]);
