import { itemTime, scenario } from "./items.ts";

export const lookUpTime = scenario({
  description:
    "Look up the time of an item; itemTime returns the text of an Instant, which its output schema does not encode, so test reports outputSchema in Lean too, which once parsed the text",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.client.call(itemTime, { itemId: "item-1" });
  },
  then: () => [],
});
