import { emit, entity, instant, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), at: instant }, key: "id" });

export const { command, createEvent, contract, scenario } = service({
  name: "stampedTodo",
  description: "Keep the tasks with a stored time",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

const stored: number = JSON.parse('"2026-10-25T00:00:00Z"');

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, at: stored })]);

export const stampedTodo = contract({ addTask });
