import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; flow takes the always transition from a to b once and stops, because b leaves only on taskAdded; no violation",
  [at("2026-10-25T09:00:00+09:00")],
);
