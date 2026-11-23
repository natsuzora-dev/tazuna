import { externalService, instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, event, contract } = externalService({
  name: "calendar",
  description: "Answer questions about days and book them",
});

export const nextDay = query({
  callers: [],
  input: { from: instant },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
});

export const booked = event({ payload: { day: instant } });

export const cancelled = event({ payload: { day: instant } });

export const audited = event({ payload: { count: z.int() } });

export const book = command({
  callers: [],
  input: { day: instant },
  emits: [booked],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const cancel = command({
  callers: [],
  input: { day: instant },
  emits: [cancelled],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const reserve = command({
  callers: [],
  input: { day: instant },
  output: { reservationId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
