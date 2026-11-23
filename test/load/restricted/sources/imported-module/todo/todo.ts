import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { wallClock } from "../../../outside/clock.ts";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string() },
  key: "id",
});

export const { command, createEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId, title: wallClock() })],
);

export const todo = contract({ addTask });
