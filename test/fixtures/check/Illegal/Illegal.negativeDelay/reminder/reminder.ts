import { service } from "@natsuzora-dev/tazuna";

export const { machine } = service({ name: "reminder", description: "Remind before a while" });

export const reminder = machine({
  description: "Remind an hour before it starts, which no clock reaches",
  initial: "waiting",
  states: { waiting: {}, reminding: {} },
}).chart({
  states: {
    waiting: { after: { early: { delay: -3_600_000, onFired: [{ target: "reminding" }] } } },
  },
});
