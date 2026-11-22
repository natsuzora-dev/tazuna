import { parseInstant } from "@natsuzora-dev/tazuna";
import { itemCount, scenario } from "./summary.ts";

export const countItems = scenario({
  description:
    "Count the items; itemCount returns the input field owner, which its output schema does not have, so test reports outputSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Item: [] }, peers: [] },
  when: (w) => {
    w.client.call(itemCount, { owner: "me" });
  },
  then: () => [],
});
