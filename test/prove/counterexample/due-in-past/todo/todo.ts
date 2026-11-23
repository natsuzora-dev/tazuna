import { emit, entity, instant, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), dueAt: instant },
  key: "id",
  invariants: { dueInFuture: ({ record, now }) => record.dueAt >= now },
});

export const { command, createEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, dueAt: instant },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, dueAt: input.dueAt })]);

export const todoBounds = bounds({ creates: { Task: 2 } });
