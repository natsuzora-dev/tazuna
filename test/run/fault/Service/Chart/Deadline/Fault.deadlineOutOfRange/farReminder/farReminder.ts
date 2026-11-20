import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "farReminder", description: "Remind in a far future" });

export const reminder = machine({
  description: "Remind eighty million hours after it starts, past the year 9999, which the run's time cannot hold",
  initial: "waiting",
  states: { waiting: {}, reminding: { type: "final" } },
}).chart({
  states: {
    waiting: { after: { far: { delay: { hours: 80_000_000 }, onFired: [{ target: "reminding" }] } } },
  },
});
