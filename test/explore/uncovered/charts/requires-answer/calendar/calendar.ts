import { datetime, externalService } from "@natsuzora-dev/tazuna";

export const { query, contract } = externalService({ name: "calendar", description: "Answer questions about days" });

export const nextDay = query({
  input: { from: datetime },
  output: { day: datetime },
  rejects: ["requires"],
  requires: { isWeekday: ({ input }) => input.from.toZonedDateTimeISO("UTC").dayOfWeek <= 5 },
});

export const calendar = contract({ nextDay });
