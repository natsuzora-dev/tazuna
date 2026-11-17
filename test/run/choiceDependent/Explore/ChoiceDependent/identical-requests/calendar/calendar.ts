import { datetime, externalService } from "@natsuzora-dev/tazuna";

export const { query, contract } = externalService({ name: "calendar", description: "Answer date queries" });

export const nextBusinessDay = query({ input: { from: datetime }, output: { day: datetime }, rejects: [] });
