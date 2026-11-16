import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event } = service({ description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const countReported = event({
  payload: { count: z.int(), lastTaskId: z.string() },
});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const reportCount = command({
  input: { count: z.int(), lastTaskId: z.string() },
  emits: [countReported],
}).decide(({ input }) => [emit(countReported, { count: input.count, lastTaskId: input.lastTaskId })]);
