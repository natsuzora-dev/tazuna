import { bag, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { automation, command, query, machine, createEvent, updateEvent, contract, scenario } = service({
  name: "backlog",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, isDone: false })]);

export const taskTitles = query({
  callers: ["client"],
  input: { prefix: z.string() },
  output: { titles: bag(Task.fields.title) },
  requires: { notEmpty: ({ input }) => input.prefix !== "" },
}).resolve(({ input, records }) => ({
  titles: records.Task.filter((t) => t.title.startsWith(input.prefix)).map((t) => t.title),
}));

export const backlog = contract({ addTask, taskTitles });
