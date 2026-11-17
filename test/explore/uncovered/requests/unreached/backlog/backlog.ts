import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { command, query, createEvent, updateEvent, contract, scenario } = service({
  name: "backlog",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, isDone: false })]);

export const taskCompleted = updateEvent({ entity: Task, writes: ["isDone"] });

export const completeTask = command({
  input: { title: Task.fields.title },
  emits: [taskCompleted],
  binds: { task: ({ input, records }) => records.Task.filter((t) => t.title === input.title).only() },
  requires: { notDone: ({ bound }) => !bound.task.isDone },
}).decide(({ bound }) => [emit(taskCompleted, { id: bound.task.id, isDone: true })]);

export const taskRenamed = updateEvent({ entity: Task, writes: ["title"] });

export const renameTask = command({
  input: { taskId: ref(Task), title: Task.fields.title },
  emits: [taskRenamed],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
  requires: { chore: ({ input }) => input.title.startsWith("Chore") },
}).decide(({ bound, input }) => [emit(taskRenamed, { id: bound.task.id, title: input.title })]);

export const taskTitles = query({
  input: { prefix: z.string() },
  output: { titles: bag(Task.fields.title) },
  requires: {
    notEmpty: ({ input }) => input.prefix !== "",
    chore: ({ input }) => input.prefix.startsWith("Chore"),
  },
}).resolve(({ input, records }) => ({
  titles: records.Task.filter((t) => t.title.startsWith(input.prefix)).map((t) => t.title),
}));

export const backlog = contract({ addTask, completeTask, renameTask, taskTitles });
