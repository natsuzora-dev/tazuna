import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { automation, command, machine, event, contract } = service({ description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const counted = event({ payload: { taskId: z.string() } });
export const logged = event({ payload: { taskId: z.string() } });
export const archived = event({ payload: { taskId: z.string() } });
export const scheduled = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const count = command({
  input: { taskId: z.string() },
  emits: [counted],
}).decide(({ input }) => [emit(counted, { taskId: input.taskId })]);

export const log = command({
  input: { taskId: z.string() },
  emits: [logged],
}).decide(({ input }) => [emit(logged, { taskId: input.taskId })]);

export const schedule = command({
  input: { taskId: z.string() },
  emits: [scheduled],
}).decide(({ input }) => [emit(scheduled, { taskId: input.taskId })]);

export const archive = command({
  input: { taskId: z.string() },
  emits: [archived],
}).decide(({ input }) => [emit(archived, { taskId: input.taskId })]);
