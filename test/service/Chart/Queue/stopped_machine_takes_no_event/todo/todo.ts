import { emit, service } from "@natsuzora-dev/tazuna";

export const { command, event, machine, screen, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
});

export const taskAdded = event({});
export const taskFinished = event({});
export const taskArchived = event({});
export const taskDropped = event({});
export const taskLogged = event({});

export const addTask = command({ callers: ["client"], emits: [taskAdded] }).decide(() => [emit(taskAdded, {})]);
export const finishTask = command({ callers: ["client"], emits: [taskFinished] }).decide(() => [
  emit(taskFinished, {}),
]);
export const archiveTask = command({ callers: ["client"], emits: [taskFinished, taskArchived] }).decide(() => [
  emit(taskFinished, {}),
  emit(taskArchived, {}),
]);
export const dropTask = command({ callers: ["client"], emits: [taskDropped] }).decide(() => [emit(taskDropped, {})]);
export const logTask = command({ callers: ["client", "todo"], emits: [taskLogged] }).decide(() => [
  emit(taskLogged, {}),
]);
