import { datetime, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), title: z.string().min(1), completedAt: datetime.nullable() },
  key: "id",
  unique: ["title"],
});

export const { command, query, machine, createEvent, updateEvent } = service({
  description: "Keep tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const taskCompleted = updateEvent({
  entity: Task,
  writes: ["completedAt"],
});

export const taskRenamed = updateEvent({
  entity: Task,
  writes: ["title"],
});

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, completedAt: null })]);

export const completeTask = command({
  input: { taskId: ref(Task) },
  emits: [taskCompleted],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
  requires: { isOpen: ({ bound }) => bound.task.completedAt === null },
}).decide(({ input, now }) => [emit(taskCompleted, { id: input.taskId, completedAt: now })]);

export const swapTitles = command({
  input: { firstId: ref(Task), secondId: ref(Task) },
  emits: [taskRenamed],
  binds: {
    first: ({ input, records }) => records.Task.get(input.firstId),
    second: ({ input, records }) => records.Task.get(input.secondId),
  },
}).decide(({ bound }) => [
  emit(taskRenamed, { id: bound.first.id, title: bound.second.title }),
  emit(taskRenamed, { id: bound.second.id, title: bound.first.title }),
]);

export const titledCount = query({
  input: { title: z.string() },
  output: { count: z.int() },
  requires: { hasTitle: ({ input }) => input.title !== "" },
}).resolve(({ input, records }) => ({ count: records.Task.filter((t) => t.title === input.title).size }));
