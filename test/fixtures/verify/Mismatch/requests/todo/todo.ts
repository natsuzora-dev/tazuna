import { emit, entity, instant, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), dueAt: instant.nullable() },
  key: "id",
});

export const { command, machine, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, dueAt: null })]);

export const planner = machine({
  description: "Ask for the next day of the latest added task",
  receives: { taskAdded },
  queries: { nextDay: calendar.nextDay },
  initial: "idle",
  states: { idle: {}, asking: {} },
}).chart({
  on: { taskAdded: [{ target: "asking" }] },
  states: {
    asking: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "idle" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
  },
});
