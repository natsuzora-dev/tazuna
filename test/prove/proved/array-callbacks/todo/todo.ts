import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), low: z.int().min(0).max(10), high: z.int().min(0).max(10) },
  key: "id",
});

export const { command, createEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
  invariants: {
    someWithinRange: ({ records }) => records.Task.every((t) => [t.low, t.high, -1].some((p) => p >= 0 && p <= 10)),
    everyWithinRange: ({ records }) => records.Task.every((t) => [t.low, t.high].every((p) => p >= 0)),
  },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, low: Task.fields.low, high: Task.fields.high },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, low: input.low, high: input.high })]);

export const todoBounds = bounds({ creates: { Task: 2 } });
