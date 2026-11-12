import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; homeScreen opens pickScreen with count 0, and the requires positive of pickScreen throws, so test reports exception of pickScreen",
  [at("2026-10-25T09:00:00+09:00")],
);
