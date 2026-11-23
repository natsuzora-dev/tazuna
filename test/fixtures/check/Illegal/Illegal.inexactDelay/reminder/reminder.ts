import { service } from "@natsuzora-dev/tazuna";

export const { machine } = service({ name: "reminder", description: "Remind after a while" });

export const reminder = machine({
  description:
    "Remind 2^53 milliseconds after it starts, past every safe integer, and nudge half a millisecond after that",
  initial: "waiting",
  states: { waiting: {}, reminding: {}, done: {} },
}).chart({
  states: {
    waiting: { after: { day: { delay: 2 ** 53, onFired: [{ target: "reminding" }] } } },
    reminding: { after: { nudge: { delay: 0.5, onFired: [{ target: "done" }] } } },
  },
});
