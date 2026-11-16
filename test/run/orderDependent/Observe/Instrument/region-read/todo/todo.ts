import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const tasksCleared = event({});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const clearTasks = command({ emits: [tasksCleared] }).decide(() => [emit(tasksCleared, {})]);

export const tracker = machine({
  description: "Count the added tasks in one region, and remember the count of the last one in the other",
  context: { count: z.int().default(0), countAtLast: z.int().default(0) },
  receives: { taskAdded, tasksCleared },
  initial: "tracking",
  states: { tracking: { type: "parallel", states: { counting: {}, remembering: {} } } },
}).chart({
  on: { tasksCleared: [{ target: "tracking" }] },
  states: {
    counting: { on: { taskAdded: [{ assign: { count: ({ context }) => context.count + 1 } }] } },
    remembering: { on: { taskAdded: [{ assign: { countAtLast: ({ context }) => context.count } }] } },
  },
});
