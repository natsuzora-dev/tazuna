import { datetime, externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, event, contract } = externalService({
  name: "calendar",
  description: "Answer questions about days and book them",
});

export const holiday = query({
  input: { day: datetime },
  output: { isHoliday: z.boolean() },
  rejects: ["invalid-input", "requires", "unavailable"],
  requires: { startOfDay: ({ input }) => input.day.toZonedDateTimeISO("UTC").hour === 0 },
});

export const booked = event({ payload: { day: datetime } });

export const book = command({
  input: { day: datetime },
  emits: [booked],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
  requires: { startOfDay: ({ input }) => input.day.toZonedDateTimeISO("UTC").hour === 0 },
  ensures: { sameDay: ({ input, events }) => events.every((e) => e.payload.day.equals(input.day)) },
});
