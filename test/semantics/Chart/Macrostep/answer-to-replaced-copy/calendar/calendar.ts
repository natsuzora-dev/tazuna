import { datetime, externalService } from "@natsuzora-dev/tazuna";

export const { query } = externalService({ description: "Answer date queries" });

export const nextDay = query({
  input: { from: datetime },
  output: { day: datetime },
  rejects: ["invalid-input", "requires", "unavailable"],
});
