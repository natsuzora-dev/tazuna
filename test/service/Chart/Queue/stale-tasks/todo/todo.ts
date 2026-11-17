import { emit, service } from "@natsuzora-dev/tazuna";

export const { command, event, machine, screen, contract, scenario } = service({
  name: "todo",
  description: "Keep tasks",
});

export const taskAdded = event({});
export const taskFinished = event({});
export const taskArchived = event({});
export const taskDropped = event({});
export const taskLogged = event({});

export const addTask = command({ emits: [taskAdded] }).decide(() => [emit(taskAdded, {})]);
export const finishTask = command({ emits: [taskFinished] }).decide(() => [emit(taskFinished, {})]);
export const archiveTask = command({ emits: [taskFinished, taskArchived] }).decide(() => [
  emit(taskFinished, {}),
  emit(taskArchived, {}),
]);
export const dropTask = command({ emits: [taskDropped] }).decide(() => [emit(taskDropped, {})]);
export const logTask = command({ emits: [taskLogged] }).decide(() => [emit(taskLogged, {})]);
