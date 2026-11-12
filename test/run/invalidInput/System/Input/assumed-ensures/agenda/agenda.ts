import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { todo } from "../todo/contract.ts";

export const { machine } = service({ description: "Plan the days" });

export const planner = machine({
  description: "Ask for the next day",
  queries: { nextDay: calendar.nextDay },
  initial: "asking",
  states: { asking: {}, done: { type: "final" } },
}).chart({
  states: {
    asking: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const reader = machine({
  description: "Read the titles of the tasks",
  queries: { taskTitles: todo.taskTitles },
  initial: "reading",
  states: { reading: {}, done: { type: "final" } },
}).chart({
  states: {
    reading: { calls: { taskTitles: { onFulfilled: [{ target: "done" }], onRejected: [{ target: "done" }] } } },
  },
});
