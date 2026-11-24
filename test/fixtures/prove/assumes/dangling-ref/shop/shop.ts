import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Owner = entity({
  description: "An owner",
  fields: { id: z.string() },
  key: "id",
});

export const Item = entity({
  description: "An item of an owner, and whether its last check found the owner",
  fields: { id: z.string(), owner: ref(Owner), ownerSeen: z.boolean() },
  key: "id",
});

export const { command, createEvent, deleteEvent, updateEvent, bounds, scenario } = service({
  name: "shop",
  description: "Keep owners and their items",
  entities: { Owner, Item },
});

export const ownerAdded = createEvent({ entity: Owner });
export const ownerRemoved = deleteEvent({ entity: Owner });
export const itemAdded = createEvent({ entity: Item });
export const itemChecked = updateEvent({ entity: Item, writes: ["ownerSeen"] });

export const addOwner = command({
  callers: ["client"],
  input: { ownerId: Owner.fields.id },
  emits: [ownerAdded],
}).decide(({ input }) => [emit(ownerAdded, { id: input.ownerId })]);

export const removeOwner = command({
  callers: ["client"],
  input: { ownerId: ref(Owner) },
  emits: [ownerRemoved],
}).decide(({ input }) => [emit(ownerRemoved, { id: input.ownerId })]);

export const addItem = command({
  callers: ["client"],
  input: { itemId: Item.fields.id, owner: ref(Owner) },
  emits: [itemAdded],
}).decide(({ input }) => [emit(itemAdded, { id: input.itemId, owner: input.owner, ownerSeen: true })]);

export const checkItem = command({
  callers: ["client"],
  input: { itemId: ref(Item) },
  emits: [itemChecked],
  binds: { item: ({ input, records }) => records.Item.get(input.itemId) },
  ensures: { seen: ({ records, input }) => records.Item.get(input.itemId)?.ownerSeen === true },
}).decide(({ input, bound, records }) => [
  emit(itemChecked, { id: input.itemId, ownerSeen: records.Owner.get(bound.item.owner) !== undefined }),
]);

export const findOrphan = command({
  callers: ["client"],
  input: { itemId: ref(Item) },
  emits: [],
  binds: { item: ({ input, records }) => records.Item.get(input.itemId) },
  requires: { orphan: ({ bound, records }) => records.Owner.get(bound.item.owner) === undefined },
}).decide(() => []);

export const shopBounds = bounds({ creates: { Owner: 1, Item: 1 } });
