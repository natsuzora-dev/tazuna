import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), title: z.string() },
  key: "id",
});

export const { command, machine, event, createEvent, updateEvent, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const taskRenamed = updateEvent({ entity: Task, writes: ["title"] });
export const taskSelected = event({ payload: { taskId: z.string() } });
export const remindPressed = event({});
export const labelsOpened = event({});
export const notified = event({ payload: { text: z.string() } });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const renameTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskRenamed],
}).decide(({ input }) => [emit(taskRenamed, { id: input.taskId, title: input.title })]);

export const selectTask = command({ callers: ["client"], input: { taskId: ref(Task) }, emits: [taskSelected] }).decide(
  ({ input }) => [emit(taskSelected, { taskId: input.taskId })],
);

export const pressRemind = command({ callers: ["client"], emits: [remindPressed] }).decide(() => [
  emit(remindPressed, {}),
]);

export const openLabels = command({ callers: ["client"], emits: [labelsOpened] }).decide(() => [
  emit(labelsOpened, {}),
]);

export const notify = command({ callers: ["client", "todo"], input: { text: z.string() }, emits: [notified] }).decide(
  ({ input }) => [emit(notified, { text: input.text })],
);
