import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), title: z.string().min(1) },
  key: "id",
});

export const { command, query, event, createEvent, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const taskAddedRecorded = createEvent({ entity: Task });
export const taskAdded = event({ payload: { taskId: z.string() } });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded],
}).decide(({ input }) => [
  emit(taskAddedRecorded, { id: input.taskId, title: input.title }),
  emit(taskAdded, { taskId: input.taskId }),
]);

export const taskCount = query({ callers: ["client"], output: { count: z.int() } }).resolve(({ records }) => ({
  count: records.Task.size,
}));
