import { datetime, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskCompleted = event({ payload: { taskId: z.string() } });
export const dayNoted = event({ payload: { day: datetime } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const completeTask = command({
  input: { taskId: z.string() },
  emits: [taskCompleted],
}).decide(({ input }) => [emit(taskCompleted, { taskId: input.taskId })]);

export const noteDay = command({
  input: { day: datetime },
  emits: [dayNoted],
}).decide(({ input }) => [emit(dayNoted, { day: input.day })]);

export const addDoneTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded, taskCompleted],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId }), emit(taskCompleted, { taskId: input.taskId })]);
