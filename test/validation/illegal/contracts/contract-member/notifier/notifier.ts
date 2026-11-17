import { emit, service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { command, event, contract } = service({
  name: "notifier",
  description: "Notify about tasks, and lists the todo event taskAdded in its own contract",
});

export const announced = event({ payload: { taskId: todo.TaskId } });

export const announce = command({
  input: { taskId: todo.TaskId },
  emits: [announced],
}).decide(({ input }) => [emit(announced, { taskId: input.taskId })]);

export const notifier = contract({ announce, announced, taskAdded: todo.taskAdded });
