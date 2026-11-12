import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; flow alternates between a and b through always transitions without end, so test reports alwaysRounds",
  [at("2026-10-25T09:00:00+09:00")],
);
