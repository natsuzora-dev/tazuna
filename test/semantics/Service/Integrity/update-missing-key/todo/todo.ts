import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), title: z.string(), note: z.string() },
  key: "id",
});

export const { command, query, updateEvent } = service({ description: "Keep tasks", entities: { Task } });

export const taskRenamed = updateEvent({ entity: Task, writes: ["title"] });

export const renameTask = command({
  input: { taskId: z.string(), title: z.string() },
  emits: [taskRenamed],
}).decide(({ input }) => [emit(taskRenamed, { id: input.taskId, title: input.title })]);

export const taskCount = query({ output: { count: z.int() } }).resolve(({ records }) => ({
  count: records.Task.length,
}));
