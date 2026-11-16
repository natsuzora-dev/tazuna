import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; homeScreen opens pickScreen with count 0, which fails the requires positive of pickScreen, so test reports failedRequires",
  [at("2026-10-25T09:00:00+09:00")],
);
