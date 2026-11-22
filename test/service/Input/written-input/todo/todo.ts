import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, contract, given, scenario } = service({
  name: "todo",
  description: "Keep the shopping list",
});

export const itemAdded = event({ payload: { note: z.string(), qty: z.int() } });

export const addItem = command({
  input: { note: z.string(), qty: z.int().default(1) },
  emits: [itemAdded],
}).decide(({ input }) => [emit(itemAdded, { note: input.note, qty: input.qty })]);
