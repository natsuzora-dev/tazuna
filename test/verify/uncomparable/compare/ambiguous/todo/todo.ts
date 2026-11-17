import { bag, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = service({ description: "Answer questions about notes" });

export const linked = query({
  input: { links: bag(z.object({ from: z.string(), to: z.string() })) },
  output: { count: z.number() },
}).resolve(({ input }) => ({ count: input.links.size }));
