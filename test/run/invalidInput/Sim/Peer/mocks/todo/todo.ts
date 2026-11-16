import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { automation, command, createEvent, event, query } = service({
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAddedRecorded = createEvent({ entity: Task });

export const taskAdded = event({ payload: { taskId: Task.fields.id } });

export const titleAdded = event({ payload: { title: Task.fields.title } });

export const taskCompleted = event({ payload: { taskId: ref(Task) } });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded],
}).decide(({ input }) => [
  emit(taskAddedRecorded, { id: input.taskId, title: input.title }),
  emit(taskAdded, { taskId: input.taskId }),
]);

export const addTitle = command({ input: { title: Task.fields.title }, emits: [titleAdded] }).decide(({ input }) => [
  emit(titleAdded, { title: input.title }),
]);

export const taskForTitle = automation({ receives: { titleAdded }, commands: { addTask } }).send({
  input: ({ createKey, payload }) => ({ taskId: createKey(ref(Task), `title:${payload.title}`), title: payload.title }),
});

export const completeTask = command({ input: { taskId: ref(Task) }, emits: [taskCompleted] }).decide(({ input }) => [
  emit(taskCompleted, { taskId: input.taskId }),
]);

export const taskTitles = query({ output: { titles: bag(Task.fields.title) } }).resolve(({ records }) => ({
  titles: records.Task.map((t) => t.title),
}));

export const tasks = query({
  output: { tasks: bag(z.object({ taskId: ref(Task), title: Task.fields.title })) },
}).resolve(({ records }) => ({ tasks: records.Task.map((t) => ({ taskId: t.id, title: t.title })) }));
