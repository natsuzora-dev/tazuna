import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ name: "todo", description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const tasksCleared = event({});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const clearTasks = command({ emits: [tasksCleared] }).decide(() => [emit(tasksCleared, {})]);

export const tracker = machine({
  description: "Mark that a task was added, once in each region",
  context: { status: z.enum(["empty", "added"]).default("empty") },
  receives: { taskAdded, tasksCleared },
  initial: "tracking",
  states: {
    tracking: {
      type: "parallel",
      states: {
        counting: { initial: "countIdle", states: { countIdle: {}, countMarking: {}, counted: {} } },
        remembering: { initial: "rememberIdle", states: { rememberIdle: {}, rememberMarking: {}, remembered: {} } },
      },
    },
  },
}).chart({
  on: { tasksCleared: [{ target: "tracking" }] },
  states: {
    countIdle: { on: { taskAdded: [{ target: "countMarking" }] } },
    countMarking: { always: [{ target: "counted", assign: { status: () => "added" } }] },
    rememberIdle: { on: { taskAdded: [{ target: "rememberMarking" }] } },
    rememberMarking: { always: [{ target: "remembered", assign: { status: () => "added" } }] },
  },
});

export const sequencedTracker = machine({
  description: "Mark that a task was added in one region, and one microstep later in the other",
  context: { status: z.enum(["empty", "added"]).default("empty") },
  receives: { taskAdded, tasksCleared },
  initial: "tracking",
  states: {
    tracking: {
      type: "parallel",
      states: {
        counting: { initial: "countIdle", states: { countIdle: {}, countMarking: {}, counted: {} } },
        remembering: {
          initial: "rememberIdle",
          states: { rememberIdle: {}, rememberWaiting: {}, rememberMarking: {}, remembered: {} },
        },
      },
    },
  },
}).chart({
  on: { tasksCleared: [{ target: "tracking" }] },
  states: {
    countIdle: { on: { taskAdded: [{ target: "countMarking" }] } },
    countMarking: { always: [{ target: "counted", assign: { status: () => "added" } }] },
    rememberIdle: { on: { taskAdded: [{ target: "rememberWaiting" }] } },
    rememberWaiting: { always: [{ target: "rememberMarking" }] },
    rememberMarking: { always: [{ target: "remembered", assign: { status: () => "added" } }] },
  },
});
