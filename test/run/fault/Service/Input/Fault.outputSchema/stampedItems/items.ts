import { datetime, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract, scenario } = service({
  name: "stampedItems",
  description: "Look up the time of an item",
});

const stored: Temporal.Instant = JSON.parse('"2026-10-25T00:00:00Z"');

export const itemTime = query({
  input: { itemId: z.string() },
  output: { at: datetime },
}).resolve(() => ({ at: stored }));

export const stampedItems = contract({ itemTime });
