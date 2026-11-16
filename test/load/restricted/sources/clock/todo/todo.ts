import { datetime, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), createdAt: datetime },
  key: "id",
});

export const { command, createEvent, contract } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input, now }) => [emit(taskAdded, { id: input.taskId, title: input.title, createdAt: now })]);

export const addTaskFromClock = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [
  emit(taskAdded, {
    id: crypto.randomUUID(),
    title: `${input.title} ${Math.random()}`,
    createdAt: Temporal.Now.instant(),
  }),
]);

export const todo = contract({ addTask, addTaskFromClock });
