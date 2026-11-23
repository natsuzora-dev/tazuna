import { externalService, instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, event, contract } = externalService({
  name: "calendar",
  description: "Answer questions about days and keep reminders",
});

export const nextDay = query({
  callers: ["agenda"],
  input: { from: instant },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
  ensures: { afterFrom: ({ input, output }) => input.from < output.day },
});

export const reminderAdded = event({
  payload: { reminderId: z.string() },
});

export const addReminder = command({
  callers: ["alarm"],
  output: { reminderId: z.string() },
  emits: [reminderAdded],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
  ensures: {
    once: ({ events }) => events.length <= 1,
    answeredId: ({ output, events }) => events.every((e) => e.payload.reminderId === output.reminderId),
  },
});

export const reminderRemoved = event({});

export const removeReminder = command({
  callers: ["cleanup"],
  emits: [reminderRemoved],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
  ensures: { removedOnce: ({ events }) => events.length === 1 },
});
