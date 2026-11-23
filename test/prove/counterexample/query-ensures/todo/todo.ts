import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), done: z.boolean() },
  key: "id",
});

export const { command, query, createEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({ input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId, done: false }),
]);

export const openCount = query({
  output: { count: z.int() },
  ensures: { withinTasks: ({ output, records }) => output.count <= records.Task.size },
}).resolve(({ records }) => ({ count: records.Task.size + 1 }));

export const todoBounds = bounds({ creates: { Task: 2 } });
