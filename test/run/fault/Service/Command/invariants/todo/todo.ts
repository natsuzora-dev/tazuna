import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string() },
  key: "id",
  invariants: { titleNotBlank: ({ record }) => record.title.trim() !== "" },
});

export const { command, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
  invariants: {
    uniqueTitles: ({ records }) =>
      records.Task.every((t) => records.Task.filter((u) => u.title === t.title).size === 1),
  },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
  requires: {
    titleNotBlank: ({ input }) => input.title.trim() !== "",
    newTitle: ({ input, records }) => records.Task.every((t) => t.title !== input.title),
  },
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const todo = contract({ addTask });
