import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ description: "Sell items" });

export const sold = event({ payload: { item: z.string() } });

export const sell = command({ input: { item: z.string() }, emits: [sold] }).decide(({ input }) => [
  emit(sold, { item: input.item }),
]);
