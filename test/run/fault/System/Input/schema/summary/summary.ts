import { contract, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Item = entity({ description: "An item", fields: { id: z.string() }, key: "id" });

export const { query } = service({ description: "Count items", entities: { Item } });

export const itemCount = query({
  input: { owner: z.string() },
  output: { count: z.number() },
}).resolve(({ records }) => ({ count: records.Item.size }));

export const summary = contract({ itemCount });
