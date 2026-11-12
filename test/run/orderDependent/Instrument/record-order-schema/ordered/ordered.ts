import { contract, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const { command, query, createEvent } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const firstTask = query({
  output: { id: z.string().endsWith("1") },
}).resolve(({ records }) => ({ id: records.Task[0]?.id ?? "" }));

export const ordered = contract({ addTask, firstTask });
