import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), title: z.string().min(1) },
  key: "id",
});

export const { command, createEvent, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const Label = z.object({ text: Task.fields.title });

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title, label: Label.optional() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);
