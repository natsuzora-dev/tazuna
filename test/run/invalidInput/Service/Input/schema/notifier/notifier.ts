import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const { automation, command, event, scenario } = service({
  name: "notifier",
  description: "Notify about tasks",
});

export const announced = event({ payload: { taskId: z.string() } });

export const announce = command({
  input: { taskId: z.string() },
  emits: [announced],
}).decide(({ input }) => [emit(announced, { taskId: input.taskId })]);

export const announceAdded = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { announce },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });
