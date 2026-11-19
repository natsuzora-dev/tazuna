import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine, scenario } = service({ name: "agenda", description: "Plan the next day" });

export const agenda = machine({
  description: "Ask for the next day when the service starts",
  queries: { nextDay: calendar.nextDay },
  initial: "asking",
  states: { asking: {}, known: { type: "final" } },
}).chart({
  states: {
    asking: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "known" }],
          onRejected: [{ target: "known" }],
        },
      },
    },
  },
});
