import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "farReminder", description: "Remind in a far future" });

export const reminder = machine({
  description:
    "Remind the largest safe integer of milliseconds after it starts, past every safe integer, which the run's time cannot hold",
  initial: "waiting",
  states: { waiting: {}, reminding: { type: "final" } },
}).chart({
  states: {
    waiting: { after: { far: { delay: 9_007_199_254_740_991, onFired: [{ target: "reminding" }] } } },
  },
});
