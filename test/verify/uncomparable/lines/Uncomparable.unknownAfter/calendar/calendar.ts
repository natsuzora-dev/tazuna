import { externalService, instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = externalService({ name: "calendar", description: "Answer questions about days" });

export const nextDay = query({
  input: { from: instant },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
  ensures: { afterFrom: ({ input, output }) => input.from < output.day },
});

export const holiday = query({
  input: { day: instant },
  output: { isHoliday: z.boolean() },
  rejects: ["invalid-input", "requires", "unavailable"],
});
