import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { device } from "../device/contract.ts";

export const { command, event, machine, contract } = service({ name: "todo", description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskCounted = event({ payload: { taskId: z.string() } });

export const addTask = command({
  callers: ["client", "notifier"],
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const countTask = command({
  callers: ["client", "todo"],
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

export const alerter = machine({
  description: "Notify and beep for each added task",
  receives: { taskAdded },
  commands: { notify: device.notify, beep: device.beep },
  initial: "idle",
  states: { idle: {}, notifying: {}, beeping: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "notifying" }] } },
    notifying: {
      sends: { notify: { input: () => ({ text: "A task was added" }), onAccepted: [{ target: "beeping" }] } },
    },
    beeping: { sends: { beep: { onAccepted: [{ target: "idle" }], onRejected: [] } } },
  },
});
