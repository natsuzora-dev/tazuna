import { contract, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent } = service({
  description: "Keep the tasks on a board",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const flow = machine({
  description: "Alternate while a condition is met",
  receives: { taskAdded },
  initial: "a",
  states: { a: {}, b: {} },
}).chart({
  states: {
    a: { always: [{ guard: { open: ({ records }) => records.Task.length === 0 }, target: "b" }] },
    b: { on: { taskAdded: [{ target: "a" }] } },
  },
});

export const board = contract({ addTask });
