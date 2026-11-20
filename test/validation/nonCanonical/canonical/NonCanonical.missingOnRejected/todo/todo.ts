import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { device } from "../device/contract.ts";

export const { automation, command, event, contract } = service({ name: "todo", description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const notifyAdded = automation({
  receives: { taskAdded },
  commands: { notify: device.notify },
}).send({ input: () => ({ text: "A task was added" }) });

export const todo = contract({ addTask, taskAdded });
