import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario, tick } from "./ticker.ts";

export const tickTwice = scenario({
  description: "tickTwice; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.as("client").send(tick, {});
    w.client.as("client").send(tick, {});
  },
  then: () => [],
});
