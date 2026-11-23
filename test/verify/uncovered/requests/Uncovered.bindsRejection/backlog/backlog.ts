import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
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
  input: { taskId: ref(Task), title: Task.fields.title },
  emits: [taskRenamed],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
}).decide(({ bound, input }) => [emit(taskRenamed, { id: bound.task.id, title: input.title })]);

export const backlog = contract({ addTask, renameTask });
