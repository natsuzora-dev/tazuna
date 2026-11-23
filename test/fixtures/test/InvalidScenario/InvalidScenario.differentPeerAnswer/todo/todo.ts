import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { notifier } from "../notifier/contract.ts";

export const { automation, command, event, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks and notify about them",
});

export const taskAdded = event({ payload: { taskId: z.string() } });

export const addTask = command({ callers: ["client"], input: { taskId: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { taskId: input.taskId })],
);

export const notifyAdded = automation({
  receives: { taskAdded },
  commands: { notify: notifier.notify },
}).send({ input: ({ payload }) => ({ text: payload.taskId }), onRejected: [] });
