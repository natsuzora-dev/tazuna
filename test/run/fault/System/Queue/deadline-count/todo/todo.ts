import { service } from "@natsuzora-dev/tazuna";

export const { machine } = service({ description: "Keep the tasks" });

export const ticker = machine({
  description: "Tick every minute",
  initial: "ticking",
  states: { ticking: {} },
}).chart({
  states: {
    ticking: { after: { minute: { delay: { minutes: 1 }, onFired: [{ target: "ticking", reenter: true }] } } },
  },
});
