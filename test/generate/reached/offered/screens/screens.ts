import { service } from "@natsuzora-dev/tazuna";
import { store } from "../store/store.ts";

export const { screen } = service({ name: "screens", description: "List the items" });

// The answer to items opens finish only when it lists an item that is not done.
export const listScreen = screen({
  description: "The item list",
  queries: { items: store.items },
  controls: { finish: { label: "Finish", payload: { itemId: store.ItemId } } },
  initial: "listing",
  states: { listing: {}, finished: {} },
}).chart({
  offers: {
    finish: ({ shown }) => (shown.items?.items ?? []).filter((i) => !i.done).map((i) => ({ itemId: i.itemId })),
  },
  states: {
    listing: { shows: { items: {} }, on: { finish: [{ target: "finished" }] } },
  },
});
