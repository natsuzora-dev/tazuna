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

export const flowWithRequiredReenter = machine({
  description: "Count the added tasks in turn",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, busy: { initial: "first", states: { first: {}, second: {} } } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "busy" }] } },
    busy: { on: { taskAdded: [{ target: "second", reenter: false }] } },
    first: { on: { taskAdded: [{ target: "first", reenter: true }] } },
    second: { on: { taskAdded: [{ target: "busy" }] } },
  },
});

export const flow = machine({
  description: "Count the added tasks in turn, writing reenter where it must not and leaving it out where it must",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, busy: { initial: "first", states: { first: {} } } },
}).chart({
  on: { taskAdded: [{ target: "idle", reenter: true }] },
  states: {
    idle: { on: { taskAdded: [{ target: "busy", reenter: true }] } },
    busy: { on: { taskAdded: [{ target: "busy" }] } },
    first: { on: { taskAdded: [{ target: "busy", reenter: false }] } },
  },
});

export const todo = contract({ addTask });
