import { datetime, emit, entity, service } from "@natsuzora-dev/tazuna";
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
  description:
    "Ask for the next day of an added task, for a reminder and for a plan, and whether each day is a holiday",
  context: { reminderDay: datetime.nullable().default(null), planDay: datetime.nullable().default(null) },
  receives: { taskAdded },
  queries: { nextDay: calendar.nextDay, holiday: calendar.holiday },
  initial: "idle",
  states: {
    idle: {},
    asking: {
      type: "parallel",
      states: {
        reminder: {
          initial: "reminderAsking",
          states: { reminderAsking: {}, reminderChecking: { held: { day: datetime } } },
        },
        plan: { initial: "planAsking", states: { planAsking: {}, planChecking: { held: { day: datetime } } } },
      },
    },
  },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "asking" }] } },
    reminderAsking: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "reminderChecking", assign: { reminderDay: ({ output }) => output.day } }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
    reminderChecking: {
      holds: { day: ({ context }) => context.reminderDay },
      calls: {
        holiday: { input: ({ held }) => ({ day: held.day }), onFulfilled: [], onRejected: [{ target: "idle" }] },
      },
    },
    planAsking: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "planChecking", assign: { planDay: ({ output }) => output.day } }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
    planChecking: {
      holds: { day: ({ context }) => context.planDay },
      calls: {
        holiday: { input: ({ held }) => ({ day: held.day }), onFulfilled: [], onRejected: [{ target: "idle" }] },
      },
    },
  },
});
