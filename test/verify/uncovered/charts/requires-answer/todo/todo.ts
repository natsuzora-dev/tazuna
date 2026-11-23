import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/calendar.ts";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const { command, machine, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const planner = machine({
  description: "Ask for the next day once a task is added",
  receives: { taskAdded },
  queries: { nextDay: calendar.nextDay },
  initial: "idle",
  states: { idle: {}, asking: {}, planned: {}, refused: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "asking" }] } },
    asking: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "planned" }],
          onRejected: [{ target: "refused" }],
        },
      },
    },
  },
});

export const todo = contract({ addTask });
