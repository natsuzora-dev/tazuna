import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { sell } from "./shop.ts";

export const sellsItem = scenario(
  "Sell an item; ledger receives sold from the run and records it, so test reports nothing",
  [at("2026-10-25T10:00:00+09:00"), send(sell, { item: "milk" })],
);

export const sellsLongItem = scenario(
  "Sell an item with a longer name than an entry of ledger holds; ledger halts on the sold event, so test reports haltedPeer at the input that emitted it",
  [at("2026-10-25T10:00:00+09:00"), send(sell, { item: "Fresh milk" })],
);
