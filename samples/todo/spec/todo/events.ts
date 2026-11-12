import { ref } from "@natsuzora-dev/tazuna";
import { createEvent, deleteEvent, event, Settings, Task, updateEvent } from "./data.ts";

export const taskAdded = event({ payload: { taskId: ref(Task) } });

export const taskAddedRecorded = createEvent({
  entity: Task,
});

export const taskCompleted = event({
  payload: { taskId: ref(Task) },
});

export const taskCompletedRecorded = updateEvent({
  entity: Task,
  writes: ["completedAt"],
});

export const taskReopened = event({
  payload: { taskId: ref(Task) },
});

export const taskReopenedRecorded = updateEvent({
  entity: Task,
  writes: ["completedAt", "remindAt"],
});

export const taskDeleted = event({ payload: { taskId: ref(Task) } });

export const taskDeletedRecorded = deleteEvent({
  entity: Task,
});

export const dueChanged = updateEvent({
  entity: Task,
  writes: ["dueAt", "remindAt", "reminderDecision"],
});

export const dueCleared = updateEvent({
  entity: Task,
  writes: ["dueAt", "remindAt", "reminderDecision"],
});

export const reminderScheduled = updateEvent({
  entity: Task,
  writes: ["remindAt", "reminderDecision"],
});

export const reminderDecisionFailed = updateEvent({
  entity: Task,
  writes: ["reminderDecision"],
});

export const taskRenamed = updateEvent({
  entity: Task,
  writes: ["title"],
});

export const reminderTimeReached = event({
  payload: { title: Task.fields.title },
});

export const reminderTimeReachedRecorded = updateEvent({
  entity: Task,
  writes: ["remindAt"],
});

export const remindersChanged = updateEvent({
  entity: Settings,
  writes: ["shouldRemind"],
});
