import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), done: z.boolean().default(false) },
  key: "id",
});

export const { automation, command, createEvent, deleteEvent, updateEvent, contract, scenario } = service({
  description: "Keep the tasks, and mark each added task done and drop it",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const taskDone = updateEvent({ entity: Task, writes: ["done"] });

export const taskDropped = deleteEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, done: false })]);

export const markDone = command({
  input: { taskId: Task.fields.id },
  emits: [taskDone],
}).decide(({ input, records }) =>
  records.Task.get(input.taskId) === undefined ? [] : [emit(taskDone, { id: input.taskId, done: true })],
);

export const dropTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskDropped],
}).decide(({ input }) => [emit(taskDropped, { id: input.taskId })]);

export const markAddedTask = automation({
  receives: { taskAdded },
  commands: { markDone },
}).send({ input: ({ payload }) => ({ taskId: payload.id }) });

export const dropAddedTask = automation({
  receives: { taskAdded },
  commands: { dropTask },
}).send({ input: ({ payload }) => ({ taskId: payload.id }) });

export const cleanup = contract({ addTask });
