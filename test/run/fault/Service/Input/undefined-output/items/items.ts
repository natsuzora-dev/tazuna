import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Item = entity({ description: "An item", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { query, contract, scenario } = service({ description: "Look up items", entities: { Item } });

export const item = query({
  input: { itemId: z.string() },
  output: Item.fields,
}).resolve(({ input, records }) => Reflect.get(records.Item, input.itemId));

export const items = contract({ item });
