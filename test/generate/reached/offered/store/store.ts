import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Item = entity({
  description: "An item",
  fields: { id: z.string(), done: z.boolean() },
  key: "id",
});

export const { command, query, createEvent, contract, bounds } = service({
  name: "store",
  description: "Keep the items",
  entities: { Item },
});

export const itemAdded = createEvent({ entity: Item });

export const addItem = command({ callers: ["screens"], input: { itemId: Item.fields.id }, emits: [itemAdded] }).decide(
  ({ input }) => [emit(itemAdded, { id: input.itemId, done: false })],
);

export const items = query({
  callers: ["screens"],
  output: { items: bag(z.object({ itemId: ref(Item), done: Item.fields.done })) },
}).resolve(({ records }) => ({ items: records.Item.map((i) => ({ itemId: i.id, done: i.done })) }));

export const store = contract({ ItemId: ref(Item), addItem, items });

export const storeBounds = bounds({ creates: { Item: 1 } });
