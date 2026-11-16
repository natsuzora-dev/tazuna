import { datetime, externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query } = externalService({ description: "Answer date queries" });

export const nextDay = query({
  input: { from: datetime, zone: z.string() },
  output: { day: datetime },
  rejects: ["invalid-input", "requires", "unavailable"],
});
