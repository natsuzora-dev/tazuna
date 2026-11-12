import { at, call, scenario } from "@natsuzora-dev/tazuna";
import { item } from "./items.ts";

export const lookUpItem = scenario(
  "Look up an item; item reads the id as a property of the table, which has no such property, and returns undefined, which its output schema does not accept, so test reports outputSchema",
  [at("2026-10-25T09:00:00+09:00"), call(item, { itemId: "item-1" })],
);
