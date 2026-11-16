import { emit, service } from "@natsuzora-dev/tazuna";

export const { command, machine, event } = service({ description: "Keep tasks" });

export const taskAdded = event({});

export const addTask = command({ emits: [taskAdded] }).decide(() => [emit(taskAdded, {})]);
