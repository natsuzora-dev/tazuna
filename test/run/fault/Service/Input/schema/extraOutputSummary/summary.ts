import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Item = entity({ description: "An item", fields: { id: z.string() }, key: "id" });

export const { query, contract, scenario } = service({
  name: "extraOutputSummary",
  description: "Count items, returning the input with the count",
  entities: { Item },
});

export const itemCount = query({
  input: { owner: z.string() },
  output: { count: z.number() },
}).resolve(({ input, records }) => ({ ...input, count: records.Item.size }));

export const extraOutputSummary = contract({ itemCount });
