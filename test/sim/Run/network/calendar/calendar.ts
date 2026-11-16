import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, contract } = externalService({ description: "Book a slot for a task" });

export const bookingConfirmed = event({ payload: { bookingId: z.string() } });

/** No service receives it. */
export const slotFreed = event({ payload: { slot: z.string() } });

export const book = command({
  input: { bookingId: z.string(), taskId: z.string() },
  output: { slot: z.string() },
  emits: [bookingConfirmed],
  rejects: ["unavailable"],
});
