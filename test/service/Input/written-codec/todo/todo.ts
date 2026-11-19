import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { ledger } from "../ledger/contract.ts";

export const { automation, command, event, contract, given, scenario } = service({
  name: "todo",
  description: "Keep the list",
});

export const itemPriced = event({ payload: { item: z.string(), cents: z.number() } });

export const priceItem = command({
  input: { item: z.string(), cents: z.number() },
  emits: [itemPriced],
}).decide(({ input }) => [emit(itemPriced, input)]);

export const priceRecorded = automation({
  receives: { itemPriced },
  commands: { record: ledger.record },
}).send({
  input: ({ payload }) => ({ byItem: { [payload.item]: payload.cents }, range: [payload.cents, payload.cents] }),
  onRejected: [],
});
