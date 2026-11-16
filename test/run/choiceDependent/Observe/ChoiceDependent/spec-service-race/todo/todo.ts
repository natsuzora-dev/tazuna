import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { stats } from "../stats/contract.ts";

export const { command, machine, event, contract } = service({ description: "Keep the tasks" });

export const taskCompleted = event({ payload: { taskId: z.string() } });
export const taskClosed = event({ payload: { taskId: z.string() } });

export const completeTask = command({
  input: { taskId: z.string() },
  emits: [taskCompleted],
}).decide(({ input }) => [emit(taskCompleted, { taskId: input.taskId })]);

export const closeTask = command({
  input: { taskId: z.string() },
  emits: [taskClosed],
}).decide(({ input }) => [emit(taskClosed, { taskId: input.taskId })]);

export const completer = machine({
  description: "Count a completed task and resume counting",
  receives: { taskCompleted },
  commands: { countCompleted: stats.countCompleted, resumeCounting: stats.resumeCounting },
  initial: "idle",
  states: { idle: {}, completing: {} },
}).chart({
  states: {
    idle: { on: { taskCompleted: [{ target: "completing" }] } },
    completing: {
      sends: {
        countCompleted: { onAccepted: [], onRejected: [] },
        resumeCounting: { onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
      },
    },
  },
});

export const closer = machine({
  description: "Count a closed task and reset the count",
  receives: { taskClosed },
  commands: { countCompleted: stats.countCompleted, resetCount: stats.resetCount },
  initial: "idle",
  states: { idle: {}, closing: {} },
}).chart({
  states: {
    idle: { on: { taskClosed: [{ target: "closing" }] } },
    closing: {
      sends: {
        countCompleted: { onAccepted: [], onRejected: [] },
        resetCount: { onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
      },
    },
  },
});
