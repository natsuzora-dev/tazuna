import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { device } from "../device/contract.ts";

export const { automation, command, event, contract } = service({ name: "todo", description: "Keep the tasks" });

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

export const countAdded = automation({
  receives: { taskAdded },
  commands: { countTask },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }), onRejected: [] });

export const notifyAdded = automation({
  receives: { taskAdded },
  commands: { notify: device.notify },
}).send({ input: () => ({ text: "A task was added" }) });

export const beepCounted = automation({
  receives: { taskCounted },
  commands: { beep: device.beep },
}).send({ onRejected: [] });
