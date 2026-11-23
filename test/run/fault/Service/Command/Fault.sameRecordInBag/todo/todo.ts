import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const Archive = entity({
  description: "A title whose tasks are archived",
  fields: { title: z.string() },
  key: "title",
});

export const { command, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task, Archive },
});

export const taskAdded = createEvent({ entity: Task });

export const titleArchived = createEvent({ entity: Archive });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const archiveTitle = command({
  callers: ["client"],
  input: { title: Archive.fields.title },
  emits: [titleArchived],
}).decide(({ input, records }) => [
  records.Task.filter((t) => t.title === input.title).map((t) => emit(titleArchived, { title: t.title })),
]);

export const todo = contract({ addTask, archiveTitle });
