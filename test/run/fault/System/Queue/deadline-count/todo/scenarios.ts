import { at, scenario } from "@natsuzora-dev/tazuna";

export const weekLater = scenario(
  "Start the service and come back a week later; more than 10000 minutes have passed, so test reports exceededDueDeadlines",
  [at("2026-10-25T09:00:00+09:00"), at("2026-11-01T09:00:00+09:00")],
);
