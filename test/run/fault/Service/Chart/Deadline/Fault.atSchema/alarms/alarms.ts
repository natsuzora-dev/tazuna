import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "alarms", description: "Ring the alarms" });

export const alarm = machine({
  description: "Ring at an instant half a millisecond past 10:00, which the run's time cannot hold",
  initial: "waiting",
  states: { waiting: {}, ringing: { type: "final" } },
}).chart({
  states: {
    waiting: {
      after: {
        ring: {
          at: () => Temporal.Instant.from("2026-10-25T01:00:00.0005Z"),
          onFired: [{ target: "ringing" }],
        },
      },
    },
  },
});
