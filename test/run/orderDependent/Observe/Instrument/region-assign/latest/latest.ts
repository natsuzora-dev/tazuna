import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({
  name: "latest",
  description: "Remember the latest task",
});

export const taskAdded = event({ payload: { taskId: z.string() } });
export const tasksCleared = event({});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const clearTasks = command({ emits: [tasksCleared] }).decide(() => [emit(tasksCleared, {})]);

export const tracker = machine({
  description: "Clear the last task in one region, and remember it in the other",
  context: { lastTaskId: z.string().nullable().default(null) },
  receives: { taskAdded, tasksCleared },
  initial: "tracking",
  states: { tracking: { type: "parallel", states: { counting: {}, remembering: {} } } },
}).chart({
  on: { tasksCleared: [{ target: "tracking" }] },
  states: {
    counting: { on: { taskAdded: [{ assign: { lastTaskId: () => null } }] } },
    remembering: { on: { taskAdded: [{ assign: { lastTaskId: ({ payload }) => payload.taskId } }] } },
  },
});
