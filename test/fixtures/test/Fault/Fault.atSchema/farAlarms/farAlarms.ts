import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "farAlarms", description: "Ring the far alarms" });

export const alarm = machine({
  description: "Ring a millisecond past the last instant that a Date holds, which the run's time cannot hold",
  initial: "waiting",
  states: { waiting: {}, ringing: { type: "final" } },
}).chart({
  states: {
    waiting: {
      after: {
        ring: {
          at: () => 8_640_000_000_000_001,
          onFired: [{ target: "ringing" }],
        },
      },
    },
  },
});
