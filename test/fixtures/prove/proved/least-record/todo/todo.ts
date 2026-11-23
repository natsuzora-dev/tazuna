import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task with a priority",
  fields: { id: z.string(), priority: z.int() },
  key: "id",
});

export const { command, createEvent, bounds } = service({
  name: "todo",
  description: "Keep one task",
  entities: { Task },
  invariants: {
    firstIsLeast: ({ records }) => {
      const first = records.Task.minBy((t) => t.priority);
      return first === undefined || records.Task.every((t) => first.priority <= t.priority);
    },
    lastIsGreatest: ({ records }) => {
      const last = records.Task.maxBy((t) => t.priority);
      return last === undefined || records.Task.every((t) => last.priority >= t.priority);
    },
  },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, priority: z.int() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, priority: input.priority })]);

export const todoBounds = bounds({ creates: { Task: 1 } });
