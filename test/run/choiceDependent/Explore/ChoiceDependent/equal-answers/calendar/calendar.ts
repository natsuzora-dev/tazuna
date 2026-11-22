import { externalService, instant } from "@natsuzora-dev/tazuna";

export const { query, contract } = externalService({ name: "calendar", description: "Answer date queries" });

export const nextBusinessDay = query({ input: { from: instant }, output: { day: instant }, rejects: [] });
