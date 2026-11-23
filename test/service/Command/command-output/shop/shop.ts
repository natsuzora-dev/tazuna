import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ name: "shop", description: "Take orders" });

export const orderPlaced = event({ payload: { amount: z.int().positive() } });
export const orderCancelled = event({});

export const placeOrder = command({
  callers: ["client"],
  input: { amount: z.int().positive() },
  emits: [orderPlaced],
}).decide(({ input }) => [emit(orderPlaced, { amount: input.amount })]);

export const cancelOrder = command({ callers: ["client"], emits: [orderCancelled] }).decide(() => [
  emit(orderCancelled, {}),
]);
