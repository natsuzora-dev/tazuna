import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine, scenario } = service({ description: "Plan the days" });

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
