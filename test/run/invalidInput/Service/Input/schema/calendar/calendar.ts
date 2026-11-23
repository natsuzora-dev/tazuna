import { externalService, instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, contract } = externalService({
  name: "calendar",
  description: "Answer questions about days and book them",
});

export const nextDay = query({
  callers: ["agenda"],
  input: { from: instant },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
  ensures: { afterFrom: ({ input, output }) => input.from < output.day },
});

export const holiday = query({
  callers: [],
  input: { day: instant },
  output: { isHoliday: z.boolean() },
  rejects: ["invalid-input", "requires", "unavailable"],
});

export const book = command({
  callers: ["booking"],
  input: { day: instant },
  output: { bookingId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
