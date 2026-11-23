import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, createEvent, deleteEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const taskDeleted = deleteEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const deleteBoundTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [taskDeleted],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
}).decide(({ bound }) => [emit(taskDeleted, { id: bound.task.id })]);

export const deleteTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [taskDeleted],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
}).decide(({ input }) => [emit(taskDeleted, { id: input.taskId })]);

export const todo = contract({ addTask, deleteBoundTask, deleteTask });
