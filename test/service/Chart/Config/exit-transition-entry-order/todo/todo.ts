import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ name: "todo", description: "Keep tasks" });

export const taskAdded = event({});
export const taskCompleted = event({});
export const taskRemoved = event({});
export const taskRenamed = event({});
export const stepsRecorded = event({ payload: { steps: z.array(z.string()) } });

export const addTask = command({ emits: [taskAdded] }).decide(() => [emit(taskAdded, {})]);

export const completeTask = command({ emits: [taskCompleted] }).decide(() => [emit(taskCompleted, {})]);

export const removeTask = command({ emits: [taskRemoved] }).decide(() => [emit(taskRemoved, {})]);

export const renameTask = command({ emits: [taskRenamed] }).decide(() => [emit(taskRenamed, {})]);

export const recordSteps = command({
  input: { steps: z.array(z.string()) },
  emits: [stepsRecorded],
}).decide(({ input }) => [emit(stepsRecorded, { steps: input.steps })]);
