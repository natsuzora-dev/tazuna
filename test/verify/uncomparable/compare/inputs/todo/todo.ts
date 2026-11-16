import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent, contract, scenario } = service({
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const planner = machine({
  description: "Ask for the next day when a task is added",
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

export const todo = contract({ addTask });
