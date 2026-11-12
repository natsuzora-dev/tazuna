import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; listScreen opens pickScreen, which closes with the count itself and fails its ensures belowCount, so test reports failedEnsures",
  [at("2026-10-25T09:00:00+09:00")],
);
