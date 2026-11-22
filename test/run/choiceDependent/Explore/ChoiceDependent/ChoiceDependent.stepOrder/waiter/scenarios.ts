import { parseInstant } from "@natsuzora-dev/tazuna";
import { go, scenario } from "./waiter.ts";

export const once = scenario({
  description:
    "go emits e1 and e2 unordered. e1 enters waiting, whose at reads due, and e2 sets due to 06:00. Taking e1 first fixes the deadline at 05:00 and pings by 05:30; taking e2 first fixes it at 06:00. No line of go tells the orders apart, and the pending deadlines do, so test reports stepOrder",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Once: { went: false } }, peers: [] },
  when: (w) => {
    w.client.send(go, { ks: ["1", "2"] });
    w.clock.at(parseInstant("2026-10-25T05:30:00Z"));
  },
  then: () => [],
});
