import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Item = entity({ description: "An item", fields: { id: z.string() }, key: "id" });

export const { query, contract, scenario } = service({
  name: "extraOutputSummary",
  description: "Count items, returning the input with the count",
  entities: { Item },
});

export const itemCount = query({
  callers: ["client"],
  input: { owner: z.string() },
  output: { count: z.int() },
}).resolve(({ input, records }) => {
  // A const, which tsc does not check for fields that the output lacks, as it checks a returned object literal.
  const answer = { owner: input.owner, count: records.Item.size };
  return answer;
});

export const extraOutputSummary = contract({ itemCount });
