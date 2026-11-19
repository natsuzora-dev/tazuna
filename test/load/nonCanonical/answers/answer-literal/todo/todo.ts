import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string().min(1) },
  key: "id",
});

export const { command, createEvent, event, query, contract, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const taskRecorded = createEvent({ entity: Task });

export const taskAdded = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string(), title: z.string() },
  emits: [taskRecorded, taskAdded],
}).decide(({ input }) => [
  emit(taskRecorded, { id: input.taskId, title: input.title }),
  emit(taskAdded, { taskId: input.taskId }),
]);

export const taskCount = query({ output: { count: z.number() } }).resolve(() => ({ count: 0 }));
