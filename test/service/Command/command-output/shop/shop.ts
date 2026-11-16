import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ description: "Take orders" });

export const orderPlaced = event({ payload: { amount: z.number().int().positive() } });
export const orderCancelled = event({});

export const placeOrder = command({
  input: { amount: z.number().int().positive() },
  emits: [orderPlaced],
}).decide(({ input }) => [emit(orderPlaced, { amount: input.amount })]);

export const cancelOrder = command({
  emits: [orderCancelled],
}).decide(() => [emit(orderCancelled, {})]);
