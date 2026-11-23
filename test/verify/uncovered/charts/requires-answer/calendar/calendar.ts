import { externalService, instant, parseInstant } from "@natsuzora-dev/tazuna";

// The weekdays of the week that the scenarios use; a calendar knows them, and tazuna computes no calendar.
const monday = parseInstant("2026-10-26T00:00:00Z");
const saturday = parseInstant("2026-10-31T00:00:00Z");

export const { query, contract } = externalService({ name: "calendar", description: "Answer questions about days" });

export const nextDay = query({
  input: { from: instant },
  output: { day: instant },
  rejects: ["requires"],
  requires: { isWeekday: ({ input }) => monday <= input.from && input.from < saturday },
});

export const calendar = contract({ nextDay });
