import { externalService, instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = externalService({ name: "calendar", description: "Answer date queries" });

export const nextDay = query({
  input: { from: instant, constructor: z.object({ name: z.string() }) },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
});
