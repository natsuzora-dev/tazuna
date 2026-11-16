import { datetime, externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, event, contract } = externalService({
  description: "Answer questions about days and keep reminders",
});

export const nextDay = query({
  input: { from: datetime },
  output: { day: datetime },
  rejects: ["invalid-input", "requires", "unavailable"],
  requires: { isWeekday: ({ input }) => input.from.toZonedDateTimeISO("UTC").dayOfWeek <= 5 },
  ensures: { afterFrom: ({ input, output }) => Temporal.Instant.compare(input.from, output.day) < 0 },
});

export const reminderAdded = event({
  payload: { reminderId: z.string() },
});

export const addReminder = command({
  emits: [reminderAdded],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
  ensures: { isOnce: ({ events }) => events.length <= 1 },
});
