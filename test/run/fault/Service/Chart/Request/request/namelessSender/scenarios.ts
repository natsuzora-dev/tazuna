import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; greeter sends greet with an empty name, which fails the input schema of greet, so test reports requestInputSchema",
  [at("2026-10-25T09:00:00+09:00")],
);
