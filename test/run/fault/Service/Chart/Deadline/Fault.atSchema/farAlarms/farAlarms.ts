import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "farAlarms", description: "Ring the far alarms" });

export const alarm = machine({
  description: "Ring at 2^53 milliseconds, past every safe integer, which the run's time cannot hold",
  initial: "waiting",
  states: { waiting: {}, ringing: { type: "final" } },
}).chart({
  states: {
    waiting: {
      after: {
        ring: {
          at: () => 9_007_199_254_740_992,
          onFired: [{ target: "ringing" }],
        },
      },
    },
  },
});
