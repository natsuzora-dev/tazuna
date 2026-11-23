import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./levels.ts";

export const start = scenario({
  description:
    "Start the service; the entry assign of raising writes the level 3, above the maximum 2, so test reports contextSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
