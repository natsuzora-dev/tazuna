import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { shop } from "../shop/contract.ts";

export const Entry = entity({
  description: "A sold item",
  fields: { id: z.string(), item: z.string().max(8) },
  key: "id",
});

export const { automation, command, createEvent } = service({ description: "Record the sales", entities: { Entry } });

export const entryRecorded = createEvent({ entity: Entry });

export const record = command({
  input: { entryId: ref(Entry), item: Entry.fields.item },
  emits: [entryRecorded],
}).decide(({ input }) => [emit(entryRecorded, { id: input.entryId, item: input.item })]);

export const recordSold = automation({ receives: { sold: shop.sold }, commands: { record } }).send({
  input: ({ createKey, payload }) => ({ entryId: createKey(ref(Entry)), item: payload.item }),
});
