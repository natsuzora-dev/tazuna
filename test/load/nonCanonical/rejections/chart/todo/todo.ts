import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, machine } = service({ description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskCounted = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const countTask = command({
  input: { taskId: z.string() },
  emits: [taskCounted],
}).decide(({ input }) => [emit(taskCounted, { taskId: input.taskId })]);

export const counter = machine({
  description: "Count each added task",
  receives: { taskAdded },
  commands: { countTask },
  initial: "idle",
  states: { idle: {}, counting: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "counting" }] } },
    counting: {
      sends: { countTask: { input: () => ({ taskId: "task-1" }), onAccepted: [{ target: "idle" }], onRejected: [] } },
    },
  },
});
