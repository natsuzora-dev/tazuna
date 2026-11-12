import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const { automation, command, event } = service({ description: "Notify about tasks" });

export const followUpAdded = event({ payload: { taskId: z.string() } });

export const addFollowUp = command({
  input: { taskId: z.string() },
  emits: [followUpAdded],
}).decide(({ input }) => [emit(followUpAdded, { taskId: input.taskId })]);

export const addTaskForFollowUp = automation({
  receives: { followUpAdded },
  commands: { addTask: todo.addTask },
}).send({ input: ({ payload }) => ({ taskId: `${payload.taskId}-follow-up` }) });
