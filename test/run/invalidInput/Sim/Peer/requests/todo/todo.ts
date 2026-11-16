import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), seen: z.boolean() },
  key: "id",
});

export const { command, createEvent, event, query, updateEvent, contract } = service({
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAddedRecorded = createEvent({ entity: Task });

export const taskSeenRecorded = updateEvent({ entity: Task, writes: ["seen"] });

export const taskAdded = event({ payload: { taskId: Task.fields.id } });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded],
}).decide(({ input }) => [
  emit(taskAddedRecorded, { id: input.taskId, title: input.title, seen: false }),
  emit(taskAdded, { taskId: input.taskId }),
]);

export const markSeen = command({ input: { taskId: ref(Task) }, emits: [taskSeenRecorded] }).decide(({ input }) => [
  emit(taskSeenRecorded, { id: input.taskId, seen: true }),
]);

export const tasks = query({
  output: { tasks: bag(z.object({ taskId: ref(Task), title: Task.fields.title, seen: Task.fields.seen })) },
}).resolve(({ records }) => ({ tasks: records.Task.map((t) => ({ taskId: t.id, title: t.title, seen: t.seen })) }));
