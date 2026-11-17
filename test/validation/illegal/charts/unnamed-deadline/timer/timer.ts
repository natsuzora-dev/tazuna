import { service } from "@natsuzora-dev/tazuna";

export const { machine, contract } = service({ name: "timer", description: "Ring once" });

const later = { late: { delay: { hours: 2 }, onFired: [] } };

export const ringing = machine({
  description: "A timer whose body spreads in a deadline late that the tree does not name",
  initial: "waiting",
  states: { waiting: { after: ["soon"] }, rung: { type: "final" } },
}).chart({
  states: { waiting: { after: { soon: { delay: { hours: 1 }, onFired: [{ target: "rung" }] }, ...later } } },
});
