import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = service({ name: "todo", description: "Answer questions about notes" });

export const notesIn = query({
  input: { ids: z.array(z.string()) },
  output: { count: z.number() },
}).resolve(({ input }) => ({ count: input.ids.length }));

export const note = query({
  input: { id: z.string() },
  output: { found: z.boolean() },
}).resolve(() => ({ found: false }));

export const notesNamed = query({
  input: { prefix: z.string() },
  output: { count: z.number() },
}).resolve(() => ({ count: 0 }));
