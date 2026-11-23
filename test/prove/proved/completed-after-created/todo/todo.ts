import { emit, entity, instant, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), createdAt: instant, completedAt: instant.nullable() },
  key: "id",
  invariants: {
    createdBeforeNow: ({ record, now }) => record.createdAt <= now,
    completedAfterCreated: ({ record }) => record.completedAt === null || record.completedAt >= record.createdAt,
  },
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const taskCompleted = updateEvent({ entity: Task, writes: ["completedAt"] });

export const addTask = command({ input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(({ input, now }) => [
  emit(taskAdded, { id: input.taskId, createdAt: now, completedAt: null }),
]);

export const completeTask = command({ input: { taskId: ref(Task) }, emits: [taskCompleted] }).decide(
  ({ input, now }) => [emit(taskCompleted, { id: input.taskId, completedAt: now })],
);

export const todoBounds = bounds({ creates: { Task: 2 } });
