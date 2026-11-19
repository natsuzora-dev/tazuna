import { item, scenario } from "./items.ts";

export const lookUpItem = scenario({
  description:
    "Look up an item; item reads the id as a property of the table, which has no such property, and returns undefined, which its output schema does not accept, so test reports outputSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Item: [] }, peers: [] },
  when: (w) => {
    w.client.call(item, { itemId: "item-1" });
  },
  then: () => [],
});
