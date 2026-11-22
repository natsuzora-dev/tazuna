import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./counters.ts";

export const start = scenario({
  description: "Start the service; the copy sets visits to 0, so test reports copyContextSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
