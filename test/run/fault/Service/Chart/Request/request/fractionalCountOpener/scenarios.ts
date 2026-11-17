import { scenario } from "./opener.ts";

export const start = scenario(
  "Start the service; homeScreen opens pickScreen with count 0.5, which fails the input schema of pickScreen, so test reports inputSchema of homeScreen",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (_w) => {},
    then: () => [],
  },
);
