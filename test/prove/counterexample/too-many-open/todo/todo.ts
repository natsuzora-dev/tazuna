import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), open: z.boolean() },
  key: "id",
});

export const { command, createEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
  invariants: { fewOpen: ({ records }) => records.Task.filter((t) => t.open).size <= 2 },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId, open: true })],
);

export const todoBounds = bounds({ creates: { Task: 3 } });
