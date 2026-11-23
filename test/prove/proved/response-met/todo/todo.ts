import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), done: z.boolean(), doneAt: z.int().nullable() },
  key: "id",
  responses: {
    stamped: { when: ({ record }) => record.done, expect: ({ record }) => record.doneAt !== null, within: 0 },
  },
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const taskCompleted = updateEvent({ entity: Task, writes: ["done", "doneAt"] });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId, done: false, doneAt: null })],
);

export const completeTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [taskCompleted],
}).decide(({ input, now }) => [emit(taskCompleted, { id: input.taskId, done: true, doneAt: now })]);

export const todoBounds = bounds({ creates: { Task: 2 } });
