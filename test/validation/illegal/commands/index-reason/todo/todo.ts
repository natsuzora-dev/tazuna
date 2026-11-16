import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, createEvent, updateEvent } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAdded = createEvent({ entity: Task });
export const taskRenamed = updateEvent({ entity: Task, writes: ["title"] });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const renameTask = command({
  input: { taskId: ref(Task), title: Task.fields.title },
  emits: [taskRenamed],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
  requires: {
    changesTitle: ({ input, bound }) => bound.task.title !== input.title,
    1: ({ input }) => input.title !== "",
  },
}).decide(({ input }) => [emit(taskRenamed, { id: input.taskId, title: input.title })]);
