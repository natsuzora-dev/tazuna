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

export const reminderWithoutEmptyKeywords = machine({
  description: "Wait an hour after each added task",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, waiting: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting" }] } },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "idle" }] } } },
  },
});

export const reminder = machine({
  description: "Wait an hour after each added task, writing guard and after as {}",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, waiting: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ guard: {}, target: "waiting" }] }, after: {} },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "idle" }] } } },
  },
});

export const todo = contract({ addTask });
