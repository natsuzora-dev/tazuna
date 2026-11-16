import { contract, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

// held is typed as a Record so that any name type-checks.
const title = (args: { readonly held: Readonly<Record<string, { readonly title: string }>> }) =>
  args.held["task"]?.title ?? "";
const latestTitle = (args: { readonly held: Readonly<Record<string, { readonly title: string }>> }) =>
  args.held["latest"]?.title ?? "";

export const firstTaskWatcher = machine({
  description: "Watch the first task",
  context: { title: z.string().default("") },
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, watching: { held: { task: z.object(Task.fields) } } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "watching" }] } },
    watching: {
      holds: { task: ({ records }) => records.Task.only() },
      entry: { assign: { title } },
      on: { taskAdded: [{ target: "idle" }] },
    },
  },
});

export const watcher = machine({
  description: "Watch the first task, reading a held value that no state holds",
  context: { title: z.string().default("") },
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, watching: { held: { task: z.object(Task.fields) } } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "watching" }] } },
    watching: {
      holds: { task: ({ records }) => records.Task.only() },
      entry: { assign: { title: latestTitle } },
      on: { taskAdded: [{ target: "idle" }] },
    },
  },
});

export const todo = contract({ addTask });
