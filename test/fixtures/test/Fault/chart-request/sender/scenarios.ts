import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./sender.ts";

export const start = scenario({
  description: "Start the service; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
