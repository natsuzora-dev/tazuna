import { contract, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, query, createEvent } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const taskNamed = query({
  input: { title: Task.fields.title },
  output: { taskId: Task.fields.id.nullable() },
}).resolve(({ input, records }) => ({
  taskId: records.Task.filter((t) => t.title === input.title).only()?.id ?? null,
}));

export const todo = contract({ addTask, taskNamed });
