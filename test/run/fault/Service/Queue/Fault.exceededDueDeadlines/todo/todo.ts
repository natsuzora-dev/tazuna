import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "todo", description: "Keep the tasks" });

export const ticker = machine({
  description: "Tick every minute",
  initial: "ticking",
  states: { ticking: {} },
}).chart({
  states: {
    ticking: { after: { minute: { delay: 60_000, onFired: [{ target: "ticking", reenter: true }] } } },
  },
});
