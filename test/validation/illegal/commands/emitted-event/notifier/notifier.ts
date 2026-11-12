import { contract, emit, service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { command, event } = service({ description: "Notify about tasks" });

export const announced = event({});

export const announceWithOwnEvent = command({
  input: { taskId: todo.TaskId },
  emits: [announced],
}).decide(() => [emit(announced, {})]);

export const announce = command({
  input: { taskId: todo.TaskId },
  emits: [todo.taskAdded],
}).decide(({ input }) => [emit(todo.taskAdded, { taskId: input.taskId, title: "" })]);

export const notifier = contract({ announceWithOwnEvent, announce });
