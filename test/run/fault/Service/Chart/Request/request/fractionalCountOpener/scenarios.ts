import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./opener.ts";

export const start = scenario({
  description:
    "Start the service; homeScreen opens pickScreen with count 0.5, which fails the input schema of pickScreen, so test reports inputSchema of homeScreen",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
