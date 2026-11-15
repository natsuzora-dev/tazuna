import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { sell } from "./shop.ts";

export const sellsItem = scenario(
  "Sell an item; ledger receives sold from the run and records it, so test reports nothing",
  [at("2026-10-25T10:00:00+09:00"), send(sell, { item: "milk" })],
);

export const sellsKeyLikeItem = scenario(
  "Sell an item named like a key that ledger creates; ledger halts on the sold event with uncreatedKey, so test reports haltedPeer at the input that emitted it",
  [at("2026-10-25T10:00:00+09:00"), send(sell, { item: "Entry-1" })],
);
