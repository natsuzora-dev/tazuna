import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), done: z.boolean(), priority: z.int().min(1).max(3) },
  key: "id",
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const doneChanged = updateEvent({ entity: Task, writes: ["done"] });
export const priorityChanged = updateEvent({ entity: Task, writes: ["priority"] });

export const addTask = command({ input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId, done: false, priority: 2 }),
]);

// A ref input names a record, or the command rejects it as not-found before its binds, so the binding is never null.
export const completeTask = command({
  input: { taskId: ref(Task) },
  emits: [doneChanged],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
}).decide(({ bound }) => [emit(doneChanged, { id: bound.task.id, done: true })]);

// The input's schema keeps the priority within 1 to 3, so the requires never holds.
export const escalateTask = command({
  input: { taskId: ref(Task), priority: Task.fields.priority },
  emits: [priorityChanged],
  requires: { aboveScale: ({ input }) => input.priority > 3 },
}).decide(({ input }) => [emit(priorityChanged, { id: input.taskId, priority: input.priority })]);

export const todoBounds = bounds({ creates: { Task: 1 } });
