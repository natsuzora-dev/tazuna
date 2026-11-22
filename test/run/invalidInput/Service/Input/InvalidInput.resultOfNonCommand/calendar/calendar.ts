import { externalService, instant } from "@natsuzora-dev/tazuna";

export const { query, event, contract } = externalService({
  name: "calendar",
  description: "Answer the next day and tell when days change",
});

export const nextDay = query({
  input: { from: instant },
  output: { day: instant },
  rejects: ["invalid-input", "requires", "unavailable"],
});

export const dayChanged = event({});
