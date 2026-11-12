import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; recentScreen shows recent with limit 0, which fails the input schema of recent, so test reports showsInputSchema",
  [at("2026-10-25T09:00:00+09:00")],
);
