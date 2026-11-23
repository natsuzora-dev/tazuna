import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./board.ts";

export const start = scenario({
  description:
    "Start the service; flow takes the always transition from a to b once and stops, because b leaves only on taskAdded; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (_w) => {},
  then: () => [],
});
