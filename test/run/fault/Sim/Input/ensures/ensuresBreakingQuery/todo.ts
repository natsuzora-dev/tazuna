import { contract, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, query, createEvent } = service({
  description: "Keep the tasks while breaking the ensures of taskTitles",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const taskCount = query({
  output: { count: z.number() },
  ensures: { countsTasks: ({ output, records }) => output.count === records.Task.size },
}).resolve(({ records }) => ({ count: records.Task.size + 1 }));

export const ensuresBreakingQuery = contract({ addTask, taskCount });
