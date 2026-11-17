import { bag, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { command, query, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const taskIds = query({
  output: { taskIds: bag(Task.fields.id) },
}).resolve(({ records }) => ({ taskIds: records.Task.map((t) => t.id) }));

export const taskCount = query({
  output: { count: z.int() },
}).resolve(({ records }) => ({ count: records.Task.size }));

export const hasTasks = query({
  output: { hasTasks: z.boolean() },
}).resolve(({ records }) => ({ hasTasks: records.Task.size > 0 }));

export const isLate = query({
  output: { late: z.boolean() },
}).resolve(({ now }) => ({ late: Temporal.Instant.compare(now, Temporal.Instant.from("2026-10-25T02:00:00Z")) >= 0 }));
