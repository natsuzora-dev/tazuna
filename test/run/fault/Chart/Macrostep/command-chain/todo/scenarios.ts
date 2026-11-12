import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; counter sends count on every counted without a guard, which makes a chain of more than 100 commands, so test reports commandDepth",
  [at("2026-10-25T09:00:00+09:00")],
);
