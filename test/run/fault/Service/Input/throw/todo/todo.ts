import { addDays, date, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, query, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const taskTitle = query({
  input: { taskId: Task.fields.id },
  output: { title: Task.fields.title.nullable() },
}).resolve(({ input, records }) => ({ title: records.Task.get(input.taskId)?.title ?? null }));

export const dueAfter = query({
  input: { from: date, days: z.int() },
  output: { due: date },
}).resolve(({ input }) => ({ due: addDays(input.from, input.days) }));

export const todo = contract({ addTask, taskTitle, dueAfter });
