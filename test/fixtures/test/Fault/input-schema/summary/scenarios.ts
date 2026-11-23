import { parseInstant } from "@natsuzora-dev/tazuna";
import { itemCount, scenario } from "./summary.ts";

export const countItems = scenario({
  description: "Count the items; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Item: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").call(itemCount, { owner: "me" });
  },
  then: () => [],
});
