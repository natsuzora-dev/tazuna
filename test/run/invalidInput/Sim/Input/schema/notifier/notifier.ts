import { emit, service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { automation, command, event } = service({ description: "Notify about tasks" });

export const announced = event({ payload: { taskId: todo.TaskId } });

export const announce = command({
  input: { taskId: todo.TaskId },
  emits: [announced],
}).decide(({ input }) => [emit(announced, { taskId: input.taskId })]);

export const announceAdded = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { announce },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });
