import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { command, query, createEvent, contract, scenario } = service({
  description: "Keep tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const taskCount = query({ output: { count: z.int() } }).resolve(({ records }) => ({
  count: records.Task.size,
}));
