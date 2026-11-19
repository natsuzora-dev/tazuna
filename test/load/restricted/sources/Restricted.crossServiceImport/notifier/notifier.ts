import { emit, service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { command, event, contract } = service({ name: "notifier", description: "Notify about tasks" });

export const announced = event({ payload: { taskId: todo.TaskId } });

export const announce = command({
  input: { taskId: todo.TaskId },
  emits: [announced],
}).decide(({ input }) => [emit(announced, { taskId: input.taskId })]);

export const notifier = contract({ announce, announced });
