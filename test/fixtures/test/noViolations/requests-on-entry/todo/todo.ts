import { emit, instant, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
});

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskCompleted = event({ payload: { taskId: z.string() } });
export const dayNoted = event({ payload: { day: instant } });

export const addTask = command({ callers: ["client"], input: { taskId: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { taskId: input.taskId })],
);

export const completeTask = command({
  callers: ["client"],
  input: { taskId: z.string() },
  emits: [taskCompleted],
}).decide(({ input }) => [emit(taskCompleted, { taskId: input.taskId })]);

export const noteDay = command({ callers: ["client", "todo"], input: { day: instant }, emits: [dayNoted] }).decide(
  ({ input }) => [emit(dayNoted, { day: input.day })],
);

export const addDoneTask = command({
  callers: ["client"],
  input: { taskId: z.string() },
  emits: [taskAdded, taskCompleted],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId }), emit(taskCompleted, { taskId: input.taskId })]);
