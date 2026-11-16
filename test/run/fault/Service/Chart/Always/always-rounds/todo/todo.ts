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

export const flow = machine({
  description: "Alternate through always transitions while no task exists",
  receives: { taskAdded },
  initial: "a",
  states: { a: {}, b: {} },
}).chart({
  states: {
    a: { always: [{ guard: { open: ({ records }) => records.Task.size === 0 }, target: "b" }] },
    b: { always: [{ guard: { open: ({ records }) => records.Task.size === 0 }, target: "a" }] },
  },
});

export const todo = contract({ addTask });
