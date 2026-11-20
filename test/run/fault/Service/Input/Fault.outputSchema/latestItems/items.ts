import { service, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract, scenario } = service({
  name: "latestItems",
  description: "List the items up to a size",
});

const sizes = sortedBy(z.object({ size: z.int() }), "size").refine((xs) => (xs.at(-1)?.size ?? 0) <= 2);

export const smallItems = query({
  input: { shelfId: z.string() },
  output: { sizes },
}).resolve(() => ({ sizes: [{ size: 3 }, { size: 1 }] }));

export const latestItems = contract({ smallItems });
