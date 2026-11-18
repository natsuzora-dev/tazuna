import { arm, scenario } from "./grouper.ts";

export const pairAtTen = scenario(
  "Arm at 09:00 and move the clock to 10:30; the deadlines of marker and pairer tie at 10:00. Either order gives the same lines in the same line order, but pair emits its two paired events in two groups before mark and in one group after, so only whether paired#2 follows paired#1 changes, and test reports stepOrder with Mismatch.after",
  {
    given: {
      start: "2026-10-25T09:00:00+09:00",
      records: {
        Mark: { set: false },
        Item: [
          { id: "a", n: 1 },
          { id: "b", n: 2 },
        ],
      },
      peers: {},
    },
    when: (w) => {
      w.client.send(arm, {});
      w.clock.at("2026-10-25T10:30:00+09:00");
    },
    then: () => [],
  },
);
