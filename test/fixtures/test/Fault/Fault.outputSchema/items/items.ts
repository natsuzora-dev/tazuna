import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Item = entity({ description: "An item", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { query, contract, scenario } = service({
  name: "items",
  description: "Look up items",
  entities: { Item },
});

export const item = query({
  callers: ["client"],
  input: { itemId: z.string() },
  output: { title: z.string().min(1) },
}).resolve(({ input, records }) => ({ title: records.Item.get(input.itemId)?.title ?? "" }));

export const items = contract({ item });
