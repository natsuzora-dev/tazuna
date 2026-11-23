import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, given, scenario } = service({
  name: "planner",
  description: "Keep tasks",
});

export const taskAdded = event({ payload: { taskId: z.string() } });
export const reminded = event({});

export const addTask = command({ callers: ["client"], input: { taskId: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { taskId: input.taskId })],
);

export const remind = command({ callers: ["client", "planner"], emits: [reminded] }).decide(() => [emit(reminded, {})]);
