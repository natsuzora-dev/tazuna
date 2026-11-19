import { scenario, tick } from "./countdown.ts";

export const tickTwice = scenario(
  "Tick twice; without a guard, the held left of counting goes below zero, which its held schema rejects, so test reports heldSchema",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
    when: (w) => {
      w.client.send(tick, {});
      w.client.send(tick, {});
    },
    then: () => [],
  },
);
