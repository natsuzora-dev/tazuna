import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; counter counts to three and stops, because its guards stop the chain; no violation",
  [at("2026-10-25T09:00:00+09:00")],
);
