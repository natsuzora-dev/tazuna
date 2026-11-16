import { datetime, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), completedAt: datetime.nullable(), note: z.string().nullable() },
  key: "id",
});

export const { command, machine, createEvent, updateEvent } = service({
  description: "Keep tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const completionChanged = updateEvent({
  entity: Task,
  writes: ["completedAt"],
});
export const noted = updateEvent({ entity: Task, writes: ["note"] });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, completedAt: null, note: null })]);

export const completeTask = command({
  input: { taskId: ref(Task) },
  emits: [completionChanged],
}).decide(({ input, now }) => [emit(completionChanged, { id: input.taskId, completedAt: now })]);

export const reopenTask = command({
  input: { taskId: ref(Task) },
  emits: [completionChanged],
}).decide(({ input }) => [emit(completionChanged, { id: input.taskId, completedAt: null })]);

export const note = command({
  input: { taskId: ref(Task), text: z.string() },
  emits: [noted],
}).decide(({ input }) => [emit(noted, { id: input.taskId, note: input.text })]);
