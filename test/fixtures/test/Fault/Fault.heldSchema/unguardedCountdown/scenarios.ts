import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario, tick } from "./countdown.ts";

export const tickTwice = scenario({
  description:
    "Tick twice; without a guard, the second tick enters counting with left below zero, which its held schema rejects, so test reports heldSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.as("client").send(tick, {});
    w.client.as("client").send(tick, {});
  },
  then: () => [],
});
