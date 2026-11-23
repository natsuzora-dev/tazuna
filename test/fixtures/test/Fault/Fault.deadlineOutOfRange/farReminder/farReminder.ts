import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "farReminder", description: "Remind in a far future" });

export const reminder = machine({
  description:
    "Remind 100,000,000 days after it starts, past the last instant that a Date holds, which the run's time cannot hold",
  initial: "waiting",
  states: { waiting: {}, reminding: { type: "final" } },
}).chart({
  states: {
    waiting: { after: { far: { delay: 8_640_000_000_000_000, onFired: [{ target: "reminding" }] } } },
  },
});
