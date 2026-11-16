import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract } = service({ description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const tasksCleared = event({});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const clearTasks = command({ emits: [tasksCleared] }).decide(() => [emit(tasksCleared, {})]);

export const tracker = machine({
  description: "Count the added tasks in one region, and remember the last one in the other",
  context: { count: z.int().default(0), lastTaskId: z.string().nullable().default(null) },
  receives: { taskAdded, tasksCleared },
  initial: "tracking",
  states: { tracking: { type: "parallel", states: { counting: {}, remembering: {} } } },
}).chart({
  on: { tasksCleared: [{ target: "tracking" }] },
  states: {
    counting: { on: { taskAdded: [{ assign: { count: ({ context }) => context.count + 1 } }] } },
    remembering: { on: { taskAdded: [{ assign: { lastTaskId: ({ payload }) => payload.taskId } }] } },
  },
});
