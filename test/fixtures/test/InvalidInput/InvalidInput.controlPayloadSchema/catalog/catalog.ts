import { externalService, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = externalService({
  name: "catalog",
  description: "Answer questions about numbered items",
});

export const Item = z.strictObject({ n: z.int(), name: z.string() });

export const numbers = query({
  callers: ["shelf"],
  output: { items: sortedBy(Item, "n") },
  rejects: ["invalid-input", "requires", "unavailable"],
});
