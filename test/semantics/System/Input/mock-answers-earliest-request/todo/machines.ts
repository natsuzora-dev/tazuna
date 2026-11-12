import { calendar } from "../calendar/contract.ts";
import { machine, taskAdded } from "./todo.ts";

const done = <T extends string>(target: T): { onFulfilled: [{ target: T }]; onRejected: [{ target: T }] } => ({
  onFulfilled: [{ target }],
  onRejected: [{ target }],
});

export const planner = machine({
  description:
    "Ask calendar for the next day from now, two hours later, and one hour later, in this order, when a task is added",
  receives: { taskAdded },
  queries: { nextDay: calendar.nextDay },
  initial: "idle",
  states: {
    idle: {},
    asking: {
      type: "parallel",
      states: {
        first: { initial: "firstAsking", states: { firstAsking: {}, firstDone: { type: "final" } } },
        second: { initial: "secondAsking", states: { secondAsking: {}, secondDone: { type: "final" } } },
        later: { initial: "laterAsking", states: { laterAsking: {}, laterDone: { type: "final" } } },
      },
    },
  },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "asking" }] } },
    asking: { onDone: [{ target: "idle" }] },
    firstAsking: { calls: { nextDay: { input: ({ now }) => ({ from: now }), ...done("firstDone") } } },
    secondAsking: {
      calls: { nextDay: { input: ({ now }) => ({ from: now.add({ hours: 2 }) }), ...done("secondDone") } },
    },
    laterAsking: {
      calls: { nextDay: { input: ({ now }) => ({ from: now.add({ hours: 1 }) }), ...done("laterDone") } },
    },
  },
});
