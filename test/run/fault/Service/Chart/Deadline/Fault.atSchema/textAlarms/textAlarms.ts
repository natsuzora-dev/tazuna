import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ name: "textAlarms", description: "Ring the text alarms" });

export const alarm = machine({
  description: "Ring at an instant read from JSON, which stays a string and is no Instant",
  initial: "waiting",
  states: { waiting: {}, ringing: { type: "final" } },
}).chart({
  states: {
    waiting: {
      after: {
        ring: {
          at: () => JSON.parse('"2026-10-25T01:00:00Z"'),
          onFired: [{ target: "ringing" }],
        },
      },
    },
  },
});
