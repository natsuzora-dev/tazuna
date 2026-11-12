import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskRemoved = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskRemoved, { taskId: input.taskId })]);

export const removeTask = command({
  input: { taskId: z.string() },
  emits: [taskRemoved],
}).decide(({ input }) => [emit(taskRemoved, { taskId: input.taskId })]);
