import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event } = service({ description: "Keep the tasks, and remind of each task once" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const reminded = event({ payload: { by: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const remind = command({
  input: { by: z.string() },
  emits: [reminded],
}).decide(({ input }) => [emit(reminded, { by: input.by })]);
