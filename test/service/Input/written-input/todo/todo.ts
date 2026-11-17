import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, contract, scenario } = service({ name: "todo", description: "Keep the shopping list" });

export const itemAdded = event({ payload: { note: z.string(), qty: z.number() } });

export const addItem = command({
  input: { note: z.string().trim().toLowerCase(), qty: z.coerce.number() },
  emits: [itemAdded],
}).decide(({ input }) => [emit(itemAdded, { note: input.note, qty: input.qty })]);
