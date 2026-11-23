import { emit, service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { command, event, contract } = service({ name: "notifier", description: "Notify about tasks" });

export const announced = event({});

export const announceWithOwnEvent = command({
  callers: ["client"],
  input: { taskId: todo.TaskId },
  emits: [announced],
}).decide(() => [emit(announced, {})]);

export const announce = command({
  callers: ["client"],
  input: { taskId: todo.TaskId },
  emits: [todo.taskAdded],
}).decide(({ input }) => [emit(todo.taskAdded, { taskId: input.taskId, title: "" })]);

export const notifier = contract({ announceWithOwnEvent, announce });
