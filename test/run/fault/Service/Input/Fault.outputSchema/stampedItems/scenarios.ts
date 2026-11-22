import { parseInstant } from "@natsuzora-dev/tazuna";
import { itemTime, scenario } from "./items.ts";

export const lookUpTime = scenario({
  description:
    "Look up the time of an item; itemTime returns the ISO text of an instant, which the integer schema of its output rejects, so test reports outputSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.call(itemTime, { itemId: "item-1" });
  },
  then: () => [],
});
