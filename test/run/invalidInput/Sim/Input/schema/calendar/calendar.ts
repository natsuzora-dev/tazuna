import { datetime, externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query } = externalService({ description: "Answer questions about days and book them" });

export const nextDay = query({
  input: { from: datetime },
  output: { day: datetime },
  rejects: ["invalid-input", "requires", "unavailable"],
  ensures: { afterFrom: ({ input, output }) => Temporal.Instant.compare(input.from, output.day) < 0 },
});

export const holiday = query({
  input: { day: datetime },
  output: { isHoliday: z.boolean() },
  rejects: ["invalid-input", "requires", "unavailable"],
});

export const book = command({
  input: { day: datetime },
  output: { bookingId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
