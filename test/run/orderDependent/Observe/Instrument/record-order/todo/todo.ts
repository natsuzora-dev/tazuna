import { bag, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, query, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const titles = query({
  output: { titles: bag(z.string()) },
}).resolve(({ records }) => ({ titles: records.Task.map((t) => t.title) }));

export const titlesInArray = query({
  output: { titles: z.array(z.string()) },
}).resolve(({ records }) => {
  const titles: string[] = [];
  records.Task.map((t) => titles.push(t.title));
  return { titles };
});
