import { externalService, instant, parseInstant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

// The weekdays of the week that the scenarios use; a calendar knows them, and tazuna computes no calendar.
const monday = parseInstant("2026-10-26T00:00:00Z");
const saturday = parseInstant("2026-10-31T00:00:00Z");

export const { command, query, event, contract } = externalService({
  name: "calendar",
  description: "Answer questions about days and keep reminders",
});

export const nextDay = query({
  input: { from: instant },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
  requires: { isWeekday: ({ input }) => monday <= input.from && input.from < saturday },
  ensures: { afterFrom: ({ input, output }) => input.from < output.day },
});

export const reminderAdded = event({
  payload: { reminderId: z.string() },
});

export const addReminder = command({
  emits: [reminderAdded],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
  ensures: { isOnce: ({ events }) => events.length === 1 },
});
