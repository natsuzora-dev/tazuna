import { emit, service } from "@natsuzora-dev/tazuna";

export const { command, machine, event, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks and report when a deadline comes",
});

export const taskAdded = event({});
export const reminded = event({});

export const addTask = command({ callers: ["client"], emits: [taskAdded] }).decide(() => [emit(taskAdded, {})]);

export const remind = command({ callers: ["client", "todo"], emits: [reminded] }).decide(() => [emit(reminded, {})]);
