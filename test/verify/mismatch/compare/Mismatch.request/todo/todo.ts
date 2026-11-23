import { bag, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { screens } from "../screens/contract.ts";

export const { query, contract } = service({ name: "todo", description: "Answer questions about notes" });

export const linked = query({
  input: { links: bag(z.object({ from: screens.DraftId, to: screens.DraftId })) },
  output: { count: z.int() },
}).resolve(({ input }) => ({ count: input.links.size }));
