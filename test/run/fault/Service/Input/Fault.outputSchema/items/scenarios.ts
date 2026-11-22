import { parseInstant } from "@natsuzora-dev/tazuna";
import { item, scenario } from "./items.ts";

export const lookUpItem = scenario({
  description:
    "Look up a missing item; item answers an empty title, which its output schema does not accept, so test reports outputSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Item: [] }, peers: [] },
  when: (w) => {
    w.client.call(item, { itemId: "item-1" });
  },
  then: () => [],
});
