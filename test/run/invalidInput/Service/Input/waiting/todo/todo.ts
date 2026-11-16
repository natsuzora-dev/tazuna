import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";

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

export const planner = machine({
  description: "Ask for the next day from the time a task is added and from an hour later",
  receives: { taskAdded },
  queries: { nextDay: calendar.nextDay },
  initial: "idle",
  states: {
    idle: {},
    asking: {
      type: "parallel",
      states: {
        added: { initial: "addedWaiting", states: { addedWaiting: {}, addedDone: { type: "final" } } },
        later: { initial: "laterWaiting", states: { laterWaiting: {}, laterDone: { type: "final" } } },
      },
    },
  },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "asking" }] } },
    asking: { onDone: [{ target: "idle" }] },
    addedWaiting: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "addedDone" }],
          onRejected: [{ target: "addedDone" }],
        },
      },
    },
    laterWaiting: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now.add({ hours: 1 }) }),
          onFulfilled: [{ target: "laterDone" }],
          onRejected: [{ target: "laterDone" }],
        },
      },
    },
  },
});
