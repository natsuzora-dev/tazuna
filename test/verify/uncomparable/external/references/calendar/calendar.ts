import { datetime, externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, event } = externalService({ description: "Answer questions about days and book them" });

export const nextDay = query({
  input: { from: datetime },
  output: { day: datetime },
  rejects: ["invalid-input", "requires", "unavailable"],
});

export const booked = event({ payload: { day: datetime } });

export const cancelled = event({ payload: { day: datetime } });

export const audited = event({ payload: { count: z.number() } });

export const book = command({
  input: { day: datetime },
  emits: [booked],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const cancel = command({
  input: { day: datetime },
  emits: [cancelled],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const reserve = command({
  input: { day: datetime },
  output: { reservationId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
