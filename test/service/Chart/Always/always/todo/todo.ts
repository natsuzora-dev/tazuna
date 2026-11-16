import { bag, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });
export const Signal = entity({ description: "A signal that the user sent", fields: { id: z.string() }, key: "id" });

export const { command, machine, query, event, createEvent, deleteEvent } = service({
  description: "Keep tasks",
  entities: { Task, Signal },
});

export const taskAdded = createEvent({ entity: Task });
export const taskCompleted = deleteEvent({ entity: Task });
export const signalled = createEvent({ entity: Signal });
export const warned = event({});

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const completeTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskCompleted],
}).decide(({ input }) => [emit(taskCompleted, { id: input.taskId })]);

export const signal = command({
  input: { signalId: Signal.fields.id },
  emits: [signalled],
}).decide(({ input }) => [emit(signalled, { id: input.signalId })]);

export const warn = command({ emits: [warned] }).decide(() => [emit(warned, {})]);

export const counted = event({});
export const listed = event({});

export const count = command({ emits: [counted] }).decide(() => [emit(counted, {})]);

export const list = command({ emits: [listed] }).decide(() => [emit(listed, {})]);

export const tasks = query({ output: { taskIds: bag(z.string()) } }).resolve(({ records }) => ({
  taskIds: records.Task.map((t) => t.id),
}));

export const rowsOpened = event({});
export const rowMarked = event({ payload: { name: z.string() } });

export const openRows = command({ emits: [rowsOpened] }).decide(() => [emit(rowsOpened, {})]);

export const markRow = command({
  input: { name: z.string() },
  emits: [rowMarked],
}).decide(({ input }) => [emit(rowMarked, { name: input.name })]);
