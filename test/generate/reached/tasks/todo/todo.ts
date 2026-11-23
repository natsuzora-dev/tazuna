import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string().min(1), done: z.boolean() },
  key: "id",
});

export const { command, query, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const doneChanged = updateEvent({ entity: Task, writes: ["done"] });
export const titleChanged = updateEvent({ entity: Task, writes: ["title"] });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, done: false })]);

export const completeTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [doneChanged],
  requires: { open: ({ input, records }) => records.Task.get(input.taskId)?.done === false },
}).decide(({ input }) => [emit(doneChanged, { id: input.taskId, done: true })]);

export const reopenTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [doneChanged],
  requires: { done: ({ input, records }) => records.Task.get(input.taskId)?.done === true },
}).decide(({ input }) => [emit(doneChanged, { id: input.taskId, done: false })]);

export const renameTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [titleChanged],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
}).decide(({ bound, input }) => [emit(titleChanged, { id: bound.task.id, title: input.title })]);

export const doneCount = query({
  callers: ["client"],
  input: { atLeast: z.int() },
  output: { count: z.int() },
  requires: { notNegative: ({ input }) => input.atLeast >= 0 },
}).resolve(({ records }) => ({ count: records.Task.filter((t) => t.done).size }));

export const todoBounds = bounds({ creates: { Task: 2 } });
