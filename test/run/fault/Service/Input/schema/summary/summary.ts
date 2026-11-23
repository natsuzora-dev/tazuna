import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Item = entity({ description: "An item", fields: { id: z.string() }, key: "id" });

export const { query, contract, scenario } = service({
  name: "summary",
  description: "Count items",
  entities: { Item },
});

export const itemCount = query({
  input: { owner: z.string() },
  output: { count: z.int() },
}).resolve(({ records }) => ({ count: records.Item.size }));

export const summary = contract({ itemCount });
