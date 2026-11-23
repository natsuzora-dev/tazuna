import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent, contract, scenario } = service({
  name: "watcher",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const watcher = machine({
  description: "Watch the task that was added last",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, watching: { held: { task: z.object(Task.fields) } } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "watching", with: { task: ({ payload }) => payload } }] } },
    watching: { on: { taskAdded: [{ target: "idle" }] } },
  },
});

export const watcherContract = contract({ addTask });
