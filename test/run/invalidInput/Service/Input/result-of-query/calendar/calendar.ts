import { datetime, externalService } from "@natsuzora-dev/tazuna";

export const { query, event, contract } = externalService({
  name: "calendar",
  description: "Answer the next day and tell when days change",
});

export const nextDay = query({
  input: { from: datetime },
  output: { day: datetime },
  rejects: ["invalid-input", "requires", "unavailable"],
});

export const dayChanged = event({});
