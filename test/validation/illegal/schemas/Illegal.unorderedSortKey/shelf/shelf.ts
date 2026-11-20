import { emit, service, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ name: "shelf", description: "List items by price" });

const cents = z.codec(z.string(), z.int(), {
  decode: (text) => Math.round(Number(text) * 100),
  encode: (n) => (n / 100).toFixed(2),
});

export const itemsListed = event({
  payload: { items: sortedBy(z.object({ name: z.string(), price: cents }), "price") },
});

export const listItems = command({ emits: [itemsListed] }).decide(() => [emit(itemsListed, { items: [] })]);
