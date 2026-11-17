import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine, scenario } = service({ name: "agenda", description: "Plan the next day" });

export const agenda = machine({
  description: "Ask for the next day when the service starts, and ask again when the day changes",
  queries: { nextDay: calendar.nextDay },
  receives: { dayChanged: calendar.dayChanged },
  initial: "asking",
  states: { asking: {}, known: {} },
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
    known: { on: { dayChanged: [{ target: "asking" }] } },
  },
});
