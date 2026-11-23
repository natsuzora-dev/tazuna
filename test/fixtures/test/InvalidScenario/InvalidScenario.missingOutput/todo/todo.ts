import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), note: z.string().optional() },
  key: "id",
});

export const { command, query, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title, note: Task.fields.note },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, note: input.note })]);

export const taskTitle = query({
  callers: ["client"],
  input: { taskId: Task.fields.id },
  output: { title: Task.fields.title },
  requires: { named: ({ input }) => input.taskId !== "" },
}).resolve(({ input, records }) => ({ title: records.Task.get(input.taskId)?.title ?? "" }));

export const firstNote = query({ callers: ["client"], output: { note: Task.fields.note } }).resolve(() => ({}));
