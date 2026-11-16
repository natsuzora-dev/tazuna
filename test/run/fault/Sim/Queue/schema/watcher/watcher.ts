import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent, contract } = service({
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const watcher = machine({
  description: "Watch the first task",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, watching: { held: { task: z.object(Task.fields) } } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "watching" }] } },
    watching: { holds: { task: ({ records }) => records.Task.only() }, on: { taskAdded: [{ target: "idle" }] } },
  },
});

export const watcherContract = contract({ addTask });
