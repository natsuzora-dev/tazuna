import { parseInstant, service } from "@natsuzora-dev/tazuna";

export const { machine } = service({ name: "alarms", description: "Ring the alarms" });

export const alarm = machine({
  description: "Ring after a minute and at a fixed time at once, past the types without a written any",
  initial: "waiting",
  states: { waiting: {}, ringing: {} },
}).chart({
  states: {
    waiting: {
      after: {
        ring: JSON.parse("0") || {
          delay: 60_000,
          at: () => parseInstant("2026-10-25T00:01:00Z"),
          onFired: [{ target: "ringing" }],
        },
      },
    },
  },
});
