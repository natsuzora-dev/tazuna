import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, event, contract } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAdded = event({ payload: { taskId: ref(Task) } });

export const taskRemoved = event({ payload: { taskId: ref(Task) } });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const removeTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskRemoved],
}).decide(({ input }) => [emit(taskRemoved, { taskId: input.taskId })]);
