import { scenario } from "./screens.ts";

export const start = scenario(
  "Start the service; listScreen opens pickScreen, which closes with the count itself and fails its ensures belowCount, so test reports failedEnsures",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
    when: (_w) => {},
    then: () => [],
  },
);
