import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const todo = contract({ addTask });

export const flow = machine({
  description: "Count the added tasks in turn, leaving reenter out of a transition to its own compound source",
  receives: { taskAdded },
  initial: "busy",
  states: { busy: { initial: "first", states: { first: {}, second: {} } } },
}).chart({
  states: {
    busy: { on: { taskAdded: [{ target: "busy" }] } },
    first: { on: { taskAdded: [{ target: "second" }] } },
  },
});
