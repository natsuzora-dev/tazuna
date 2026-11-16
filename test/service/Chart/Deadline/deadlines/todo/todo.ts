import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskCompleted = event({ payload: { taskId: z.string() } });
export const reminded = event({});
export const followedUp = event({ payload: { by: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const completeTask = command({
  input: { taskId: z.string() },
  emits: [taskCompleted],
}).decide(({ input }) => [emit(taskCompleted, { taskId: input.taskId })]);

export const remind = command({ emits: [reminded] }).decide(() => [emit(reminded, {})]);

export const followUp = command({
  input: { by: z.string() },
  emits: [followedUp],
}).decide(({ input }) => [emit(followedUp, { by: input.by })]);
