import { bag, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { screens } from "../screens/contract.ts";

export const { query, contract } = service({ name: "todo", description: "Answer questions about notes" });

export const notesIn = query({
  callers: ["client", "screens"],
  input: { ids: bag(screens.DraftId) },
  output: { count: z.int() },
}).resolve(({ input }) => ({ count: input.ids.size }));

export const note = query({
  callers: ["client", "screens"],
  input: { id: screens.DraftId },
  output: { found: z.boolean() },
}).resolve(() => ({ found: false }));

export const notesNamed = query({
  callers: ["client", "screens"],
  input: { prefix: z.string() },
  output: { count: z.int() },
}).resolve(() => ({ count: 0 }));
