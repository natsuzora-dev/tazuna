import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { automation, command, query, machine, createEvent, updateEvent, contract, scenario } = service({
  name: "backlog",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, isDone: false })]);

export const taskRenamed = updateEvent({ entity: Task, writes: ["title"] });

export const renameTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskRenamed],
  requires: { chore: ({ input }) => input.title.startsWith("Chore") },
}).decide(({ input }) => [emit(taskRenamed, { id: input.taskId, title: input.title })]);

export const backlog = contract({ addTask, renameTask });
