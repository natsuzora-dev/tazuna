import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { todo } from "../todo/contract.ts";

export const { machine } = service({ description: "Plan the days" });

export const planner = machine({
  description: "Ask whether today is a holiday, then whether an hour later is",
  queries: { holiday: calendar.holiday },
  initial: "checking",
  states: { checking: {}, checkingLater: {}, done: { type: "final" } },
}).chart({
  states: {
    checking: {
      calls: {
        holiday: {
          input: ({ now }) => ({ day: now }),
          onFulfilled: [{ target: "checkingLater" }],
          onRejected: [{ target: "checkingLater" }],
        },
      },
    },
    checkingLater: {
      calls: {
        holiday: {
          input: ({ now }) => ({ day: now.add({ hours: 1 }) }),
          onFulfilled: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const reader = machine({
  description: "Read the title of a task with no id",
  queries: { taskTitle: todo.taskTitle },
  initial: "reading",
  states: { reading: {}, done: { type: "final" } },
}).chart({
  states: {
    reading: {
      calls: {
        taskTitle: {
          input: () => ({ taskId: "" }),
          onFulfilled: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
