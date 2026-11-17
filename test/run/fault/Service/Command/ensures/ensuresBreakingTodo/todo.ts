import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, createEvent, contract, scenario } = service({
  name: "ensuresBreakingTodo",
  description: "Keep the tasks while breaking the ensures of addTask",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
  ensures: { keepsTitle: ({ input, records }) => records.Task.get(input.taskId)?.title === input.title },
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title.toUpperCase() })]);

export const ensuresBreakingTodo = contract({ addTask });
