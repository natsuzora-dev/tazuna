import { contract, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { device } from "../device/contract.ts";

export const { automation, command, machine, event } = service({ description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskCompleted = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const completeTask = command({
  input: { taskId: z.string() },
  emits: [taskCompleted],
}).decide(({ input }) => [emit(taskCompleted, { taskId: input.taskId })]);

export const announceAdded = automation({
  receives: { taskAdded },
  commands: { showNotification: device.showNotification },
}).send({ input: () => ({ text: "A task was added" }), onRejected: [] });

export const announcerWithTwoEvents = machine({
  description: "Show a notification for each added or completed task",
  receives: { taskAdded, taskCompleted },
  commands: { showNotification: device.showNotification },
  initial: "announcing",
  states: { announcing: {} },
}).chart({
  states: {
    announcing: {
      on: {
        taskAdded: [{ target: "announcing", reenter: true }],
        taskCompleted: [{ target: "announcing", reenter: true }],
      },
      sends: {
        showNotification: { input: () => ({ text: "A task changed" }), onAccepted: [], onRejected: [] },
      },
    },
  },
});

export const announcer = machine({
  description: "Show a notification for each added task",
  receives: { taskAdded },
  commands: { showNotification: device.showNotification },
  initial: "announcing",
  states: { announcing: {} },
}).chart({
  states: {
    announcing: {
      on: { taskAdded: [{ target: "announcing", reenter: true }] },
      sends: {
        showNotification: { input: () => ({ text: "A task was added" }), onAccepted: [], onRejected: [] },
      },
    },
  },
});

export const todo = contract({ addTask, completeTask });
