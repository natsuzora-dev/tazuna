import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
});

export const taskAdded = event({});
export const taskCompleted = event({});
export const taskRemoved = event({});
export const taskRenamed = event({});
export const stepsRecorded = event({ payload: { steps: z.array(z.string()) } });

export const addTask = command({ callers: ["client"], emits: [taskAdded] }).decide(() => [emit(taskAdded, {})]);

export const completeTask = command({ callers: ["client"], emits: [taskCompleted] }).decide(() => [
  emit(taskCompleted, {}),
]);

export const removeTask = command({ callers: ["client"], emits: [taskRemoved] }).decide(() => [emit(taskRemoved, {})]);

export const renameTask = command({ callers: ["client"], emits: [taskRenamed] }).decide(() => [emit(taskRenamed, {})]);

export const recordSteps = command({
  callers: ["client", "todo"],
  input: { steps: z.array(z.string()) },
  emits: [stepsRecorded],
}).decide(({ input }) => [emit(stepsRecorded, { steps: input.steps })]);
