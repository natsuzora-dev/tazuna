import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const { command, query, createEvent, contract, scenario } = service({
  name: "ordered",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const firstTask = query({
  output: { id: z.string().endsWith("1") },
}).resolve(({ records }) => {
  let first: string | undefined;
  records.Task.map((t) => (first ??= t.id));
  return { id: first ?? "" };
});

export const ordered = contract({ addTask, firstTask });
