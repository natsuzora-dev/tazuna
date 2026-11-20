import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
});

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskPicked = event({ payload: { taskId: z.string() } });
export const reminded = event({ payload: { by: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const pickTask = command({
  input: { taskId: z.string() },
  emits: [taskPicked],
}).decide(({ input }) => [emit(taskPicked, { taskId: input.taskId })]);

export const remind = command({
  input: { by: z.string() },
  emits: [reminded],
}).decide(({ input }) => [emit(reminded, { by: input.by })]);
