import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string().min(1) }, key: "id" });

export const { command, event, createEvent, contract } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAddedRecorded = createEvent({ entity: Task });

export const taskAdded = event({
  payload: { taskId: ref(Task), title: Task.fields.title },
});

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded],
  requires: { short: ({ input }) => input.title.length <= 100 },
}).decide(({ input }) => [
  emit(taskAddedRecorded, { id: input.taskId, title: input.title }),
  emit(taskAdded, { taskId: input.taskId, title: input.title }),
]);
