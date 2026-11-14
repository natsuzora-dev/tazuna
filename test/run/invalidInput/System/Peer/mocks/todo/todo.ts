import { bag, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, createEvent, event, query } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAddedRecorded = createEvent({ entity: Task });

export const taskAdded = event({ payload: { taskId: Task.fields.id } });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded],
}).decide(({ input }) => [
  emit(taskAddedRecorded, { id: input.taskId, title: input.title }),
  emit(taskAdded, { taskId: input.taskId }),
]);

export const taskTitles = query({ output: { titles: bag(Task.fields.title) } }).resolve(({ records }) => ({
  titles: records.Task.map((t) => t.title),
}));
