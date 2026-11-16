import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), note: z.string().nullable() },
  key: "id",
});

export const { command, createEvent, updateEvent, contract } = service({
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const noteCopied = updateEvent({ entity: Task, writes: ["title"] });

const titles = ["Buy milk", "Walk"] as const;

export const addTask = command({
  input: { taskId: Task.fields.id, title: z.enum(titles) },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, note: null })]);

export const copyNote = command({
  input: { taskId: Task.fields.id },
  emits: [noteCopied],
  binds: { note: ({ input, records }) => records.Task.get(input.taskId)?.note },
}).decide(({ input, bound }) => [emit(noteCopied, { id: input.taskId, title: bound.note })]);

export const addTaskAsString = command({
  input: { taskId: Task.fields.id, title: z.enum(titles) },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title as string, note: null })]);

export const copyNoteAsserted = command({
  input: { taskId: Task.fields.id },
  emits: [noteCopied],
}).decide(({ input, records }) => {
  const task = records.Task.get(input.taskId) as { note: string | null };
  // biome-ignore lint/style/noNonNullAssertion: the task has a note
  return [emit(noteCopied, { id: input.taskId, title: task.note! })];
});

export const todo = contract({ addTask, copyNote, addTaskAsString, copyNoteAsserted });
