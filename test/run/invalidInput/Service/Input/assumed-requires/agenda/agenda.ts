import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine, scenario } = service({ name: "agenda", description: "Plan the days" });

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
          input: ({ now }) => ({ day: now + 3_600_000 }),
          onFulfilled: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
