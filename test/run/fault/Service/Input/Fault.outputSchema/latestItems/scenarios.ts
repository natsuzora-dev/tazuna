import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario, smallItems } from "./items.ts";

export const listSmall = scenario({
  description:
    "List the small items; smallItems builds size 3 before size 1, and its refinement reads the last size of the sorted array, so test reports outputSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.call(smallItems, { shelfId: "shelf-1" });
  },
  then: () => [],
});
