import { contract, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), tag: z.string() },
  key: "id",
});

export const { command, machine, createEvent } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, tag: Task.fields.tag },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, tag: input.tag })]);

export const tagWatcher = machine({
  description: "Watch each tag of the tasks",
  initial: "watching",
  states: { watching: { type: "map", key: { tag: Task.fields.tag }, initial: "idle", states: { idle: {} } } },
}).chart({
  states: { watching: { items: ({ records }) => records.Task.map((t) => ({ tag: t.tag })) } },
});

export const todo = contract({ addTask });
