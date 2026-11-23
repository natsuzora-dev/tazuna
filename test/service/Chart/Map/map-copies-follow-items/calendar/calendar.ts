import { externalService, instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = externalService({ name: "calendar", description: "Answer date queries" });

export const nextDay = query({
  callers: ["todo"],
  input: { from: instant, taskId: z.string() },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
});
