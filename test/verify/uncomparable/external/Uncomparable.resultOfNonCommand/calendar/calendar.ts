import { externalService, instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, event, contract } = externalService({
  name: "calendar",
  description: "Answer questions about days and book them",
});

export const nextDay = query({
  input: { from: instant },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
});

export const booked = event({ payload: { day: instant } });

export const cancelled = event({ payload: { day: instant } });

export const audited = event({ payload: { count: z.number() } });

export const book = command({
  input: { day: instant },
  emits: [booked],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const cancel = command({
  input: { day: instant },
  emits: [cancelled],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const reserve = command({
  input: { day: instant },
  output: { reservationId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
