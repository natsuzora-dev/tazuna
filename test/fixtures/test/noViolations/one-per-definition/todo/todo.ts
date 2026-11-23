import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ name: "todo", description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const greeted = event({ payload: { count: z.int() } });

export const addTask = command({ callers: ["client"], input: { taskId: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { taskId: input.taskId })],
);

export const greet = command({ callers: ["client", "todo"], input: { count: z.int() }, emits: [greeted] }).decide(
  ({ input }) => [emit(greeted, { count: input.count })],
);
