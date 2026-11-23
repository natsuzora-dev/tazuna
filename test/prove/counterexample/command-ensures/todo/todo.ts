import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), done: z.boolean() },
  key: "id",
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const doneChanged = updateEvent({ entity: Task, writes: ["done"] });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId, done: false })],
);

export const completeTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [doneChanged],
  ensures: { completed: ({ input, records }) => records.Task.get(input.taskId)?.done === true },
}).decide(({ input }) => [emit(doneChanged, { id: input.taskId, done: false })]);

export const todoBounds = bounds({ creates: { Task: 2 } });
