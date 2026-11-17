import { datetime, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), completedAt: datetime.nullable() },
  key: "id",
});

export const { command, query, event, createEvent, updateEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const taskAddedRecorded = createEvent({ entity: Task });
export const taskCompletedRecorded = updateEvent({
  entity: Task,
  writes: ["completedAt"],
});
export const taskCompleted = event({ payload: { taskId: ref(Task) } });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAddedRecorded],
}).decide(({ input }) => [emit(taskAddedRecorded, { id: input.taskId, completedAt: null })]);

export const completeTask = command({
  input: { taskId: ref(Task) },
  emits: [taskCompletedRecorded, taskCompleted],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
  requires: { isOpen: ({ bound }) => bound.task.completedAt === null },
}).decide(({ input, now }) => [
  emit(taskCompletedRecorded, { id: input.taskId, completedAt: now }),
  emit(taskCompleted, { taskId: input.taskId }),
]);
