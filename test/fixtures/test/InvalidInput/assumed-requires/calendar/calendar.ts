import { externalService, instant, parseInstant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

// The starts of the days that the scenarios use; a calendar knows them, and tazuna computes no calendar.
const day25 = parseInstant("2026-10-25T00:00:00Z");
const day26 = parseInstant("2026-10-26T00:00:00Z");

export const { command, query, event, contract } = externalService({
  name: "calendar",
  description: "Answer questions about days and book them",
});

export const holiday = query({
  callers: ["agenda"],
  input: { day: instant },
  output: { isHoliday: z.boolean() },
  rejects: ["invalid-input", "requires", "unavailable"],
  requires: { startOfDay: ({ input }) => input.day === day25 || input.day === day26 },
});

export const booked = event({ payload: { day: instant } });

export const book = command({
  callers: ["booking"],
  input: { day: instant },
  emits: [booked],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
  requires: { startOfDay: ({ input }) => input.day === day25 || input.day === day26 },
  ensures: { sameDay: ({ input, events }) => events.every((e) => e.payload.day === input.day) },
});
