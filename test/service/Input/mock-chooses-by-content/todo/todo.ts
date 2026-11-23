import { emit, service } from "@natsuzora-dev/tazuna";

export const { command, machine, event, contract, scenario } = service({ name: "todo", description: "Keep tasks" });

export const taskAdded = event({});

export const addTask = command({ callers: ["client"], emits: [taskAdded] }).decide(() => [emit(taskAdded, {})]);
