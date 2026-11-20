import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "farAlarms", description: "Ring the far alarms" });

export const alarm = machine({
  description: "Ring in the year 10000, which the run's time cannot hold",
  initial: "waiting",
  states: { waiting: {}, ringing: { type: "final" } },
}).chart({
  states: {
    waiting: {
      after: {
        ring: {
          at: () => Temporal.Instant.from("+010000-01-01T00:00:00Z"),
          onFired: [{ target: "ringing" }],
        },
      },
    },
  },
});
